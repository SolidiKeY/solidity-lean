#!/usr/bin/env python3
"""Deterministic source census, not an elaborated Lean API or proof checker.
Uses the repository's nested-comment-aware import reader; source hashes freeze
all statements, bodies, options and declarations, including generated members.
"""
import hashlib, importlib.util, json, re, subprocess, sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
def digest(data): return hashlib.sha256(data).hexdigest()
def graph(root):
    spec = importlib.util.spec_from_file_location("source_graph", root/"scripts/v08-build-graph.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.SourceGraph(root)
def assigned_paths(root):
    """Freeze the original15-file assignment; newly merged producers are not ours."""
    names = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE, "--", "Solidity/Roadmap/"], cwd=root).decode().splitlines()
    return sorted(root/name for name in names if name.endswith(".lean"))

def census(root):
    g = graph(root)
    paths = assigned_paths(root)
    unassigned = sorted(str(p.relative_to(root)) for p in (root/"Solidity/Roadmap").rglob("*.lean") if p not in set(paths))
    targets = [str(p.relative_to(root).with_suffix("")).replace("/", ".") for p in paths]
    closure = g.closure(targets)
    rows = []
    for p, name in zip(paths, targets):
        data = p.read_bytes()
        original = subprocess.check_output(["git", "show", BASE+":"+str(p.relative_to(root))], cwd=root)
        # Lexical command index aids review; full source hash is authoritative.
        commands = [{"line": i, "text": line.strip()} for i,line in enumerate(data.decode().splitlines(), 1)
                    if re.match(r"^(?:(?:private|protected|noncomputable|unsafe|partial) +)*(?:def|abbrev|theorem|lemma|structure|inductive|class|instance|opaque|axiom)\b", line)]
        rows.append(dict(module=name, path=str(p.relative_to(root)), sha256=digest(data),
                         base_sha256=digest(original), unchanged=data==original,
                         imports=g.imports(name), lexical_commands=commands,
                         budget_lines=[dict(line=i,text=line.strip()) for i,line in enumerate(data.decode().splitlines(),1)
                                       if re.search(r"maxHeartbeats|maxRecDepth|set_option", line)]))
    owned=set(targets)
    edges=[dict(consumer=m,dependency=d) for m in targets for d in g.imports(m) if d not in owned]
    return dict(base=BASE, targets=targets, modules=rows, closure=closure,
                unassigned_directory_files=unassigned,
                external_local_modules=[m for m in closure if m not in owned], boundary_edges=edges,
                reader_sha256=digest((root/"scripts/v08-build-graph.py").read_bytes()),
                note="Lexical commands are navigation aids, not an elaborated declaration census; whole-source hashes freeze all content.")
if __name__ == "__main__":
    result=census(ROOT)
    print(json.dumps(result, indent=2, sort_keys=True))
