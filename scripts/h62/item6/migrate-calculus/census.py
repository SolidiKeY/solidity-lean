#!/usr/bin/env python3
"""Deterministic source inventory, not an elaborated declaration/API proof.
Whole-file digests cover every declaration, signature, case and proof budget.
The existing graph parser is used unchanged; cycles are independently rejected.
"""
import argparse, hashlib, importlib.util, json, re, subprocess, sys
from pathlib import Path
sys.dont_write_bytecode = True
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
def digest(data): return hashlib.sha256(data).hexdigest()
def header_imports(text):
    # Only scan the header: comment delimiters in later string literals are irrelevant.
    result=[]; depth=0
    for raw in text.splitlines():
        clean=[]; index=0
        while index<len(raw):
            if depth:
                if raw.startswith("/-",index): depth+=1; index+=2
                elif raw.startswith("-/",index): depth-=1; index+=2
                else: index+=1
            elif raw.startswith("/-",index): clean.append(" "); depth=1; index+=2
            elif raw.startswith("--",index): break
            else: clean.append(raw[index]); index+=1
        line="".join(clean).strip()
        if not line or line in ("prelude","module"): continue
        found=re.fullmatch(r"(?:(?:public|private|meta) +)*import +(.+)",line)
        if not found:
            if re.match(r"(?:(?:public|private|meta) +)*import(?:$|\s)",line):
                raise ValueError("Unsupported multiline/malformed import: "+line)
            return result
        for token in found[1].split():
            if not re.fullmatch(r"[\w']+(?:\.[\w']+)*",token):
                raise ValueError("Unsupported import token: "+token)
            result.append(token)
    if depth: raise ValueError("Unterminated header comment")
    return result
def run(root, output):
    root = Path(root).resolve()
    spec = importlib.util.spec_from_file_location("graph", root/"scripts/v08-build-graph.py")
    graph_module = importlib.util.module_from_spec(spec); spec.loader.exec_module(graph_module)
    graph = graph_module.SourceGraph(root)
    graph.imports = lambda module: header_imports(graph.source(module).read_text()) if graph.source(module) else []
    names = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE, "Solidity/Calculus"], cwd=root, text=True).splitlines()
    files = [name for name in names if name.endswith(".lean")]
    targets = [name[:-5].replace("/", ".") for name in files]
    rows, edges, budgets = [], [], []
    for name, module in zip(files, targets):
        data = (root/name).read_bytes()
        frozen = subprocess.check_output(["git", "show", BASE+":"+name], cwd=root)
        imports = graph.imports(module)
        rows.append(dict(path=name, module=module, base_sha256=digest(frozen), sha256=digest(data), byte_identical=data==frozen, imports=imports))
        for imported in imports:
            if not imported.startswith("Solidity.Calculus."):
                source=graph.source(imported)
                edges.append(dict(consumer=module, dependency=imported, source=str(source.relative_to(root)) if source else None))
        for line_no, line in enumerate(data.decode().splitlines(),1):
            if any(token in line for token in ("maxHeartbeats", "maxRecDepth", "sorry", "axiom", "native_decide", "implemented_by")):
                budgets.append(dict(path=name,line=line_no,text=line))
    visiting, visited, ordered = set(), set(), []
    def visit(module):
        if module in visiting: raise ValueError("Import cycle: "+module)
        if module in visited or graph.source(module) is None: return
        visiting.add(module)
        for imported in graph.imports(module): visit(imported)
        visiting.remove(module); visited.add(module); ordered.append(module)
    for module in ["Solidity.KeySort"]+targets: visit(module)
    reverse, unparsed = [], []
    tracked = subprocess.check_output(["git","ls-files","-z"],cwd=root).decode().split("\0")
    for source in [root/name for name in sorted(tracked) if name.endswith(".lean")]:
        if source.relative_to(root).as_posix() in files: continue
        try: imports=header_imports(source.read_text())
        except ValueError as error:
            unparsed.append(dict(path=source.relative_to(root).as_posix(),error=str(error))); continue
        for imported in imports:
            if imported in targets: reverse.append(dict(consumer=source.relative_to(root).as_posix(),dependency=imported))
    result=dict(base=BASE, modules=rows, module_count=len(rows), direct_boundary_edges=edges,
        reverse_boundary_edges=reverse, reverse_scan_unparsed=unparsed, ordered_local_closure=ordered,
        closure_sources=[dict(module=m,path=graph.source(m).relative_to(root).as_posix(),sha256=digest(graph.source(m).read_bytes()),base_sha256=digest(subprocess.check_output(["git","show",BASE+":"+graph.source(m).relative_to(root).as_posix()],cwd=root))) for m in ordered],
        external_local_dependencies=[m for m in ordered if m not in targets],
        textual_budget_and_trust_hits=budgets,
        limitations="Source hashes freeze full files; textual hits include comments. No semantic API/type/axiom equivalence claim without Lean validation.")
    output=Path(output); output.mkdir(parents=True,exist_ok=True)
    (output/"census.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    (output/"source-sha256.txt").write_text("".join(r["base_sha256"]+"  "+r["path"]+"\n" for r in rows))
    (output/"ordered-modules.txt").write_text("\n".join(ordered)+"\n")
    print(json.dumps(dict(modules=len(rows),closure=len(ordered),boundary_edges=len(edges),reverse_edges=len(reverse),all_byte_identical=all(r["byte_identical"] for r in rows))))
    return result
if __name__ == "__main__":
    a=argparse.ArgumentParser(); a.add_argument("root"); a.add_argument("output"); args=a.parse_args(); run(args.root,args.output)
