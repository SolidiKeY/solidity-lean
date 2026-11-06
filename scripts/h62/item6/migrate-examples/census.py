#!/usr/bin/env python3
"""Deterministic source inventory, not an elaborated interface/axiom proof."""
import argparse, hashlib, json, pathlib, re, subprocess
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
def sha(b): return hashlib.sha256(b).hexdigest()
def inventory(root):
    files = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE], cwd=root, text=True).splitlines()
    modules = {p[:-5].replace("/", "."): p for p in files if p.endswith(".lean")}
    rows = []
    for module, path in sorted(modules.items()):
        if not path.startswith("Solidity/Examples/"): continue
        raw = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=root)
        source = raw.decode()
        # Imports are at file headers; ignore comments (including nested block comments).
        clean = strip_comments(source)
        imports = [m.group(1) for m in re.finditer(r"(?m)^[ \t]*(?:public[ \t]+|private[ \t]+)?import\s+([\w.]+)", clean)]
        # A lexical inventory only: anonymous examples, namespaces, macros and quotations
        # require elaboration to establish exact declaration identities and type equality.
        declarations = declarations_in(clean)
        rows.append({"module": module, "path": path, "source_sha256": sha(raw), "imports": imports, "external_imports": [m for m in imports if not m.startswith("Solidity.Examples.")], "lexical_declarations": declarations, "proof_budgets": re.findall(r"set_option\s+(?:maxHeartbeats|maxRecDepth)\s+\d+", clean), "trust_tokens": {word:len(re.findall(r"\b"+word+r"\b",clean)) for word in ("sorry","axiom","native_decide")}})
    edges = sorted({(row["module"],dep) for row in rows for dep in row["external_imports"]})
    return {"base":BASE,"boundary":"source hashes and lexical census; no claim of elaborated type equality", "modules":rows,"external_edges":[{"from":a,"to":b,"path":modules.get(b)} for a,b in edges]}
def declarations_in(clean):
    pattern = r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe|local|scoped|partial)[ \t]+)*(theorem|lemma|def|abbrev|inductive|structure|class|instance|example)\b[ \t]*([^\s:({\n]*)"
    return [{"line":clean[:m.start(1)].count("\n")+1, "kind":m.group(1), "name":None if m.group(1)=="example" or not m.group(2) else m.group(2)} for m in re.finditer(pattern,clean)]
def strip_comments(source):
    out=[];i=0;depth=0;string=False
    while i<len(source):
        if depth:
            if source.startswith("/-",i):depth+=1;out.extend("  ");i+=2
            elif source.startswith("-/",i):depth-=1;out.extend("  ");i+=2
            else:out.append("\n" if source[i]=="\n" else " ");i+=1
        elif string:
            out.append("\n" if source[i]=="\n" else " ")
            if source[i]=="\\" and i+1<len(source):out.append("\n" if source[i+1]=="\n" else " ");i+=2;continue
            if source[i]=='"':string=False
            i+=1
        elif source.startswith("--",i):
            end=source.find("\n",i);end=len(source) if end<0 else end
            out.extend(" "*(end-i));i=end
        elif source.startswith("/-",i):depth=1;out.extend("  ");i+=2
        else:
            if source[i]=='"':string=True
            out.append(" " if string else source[i]);i+=1
    return "".join(out)
if __name__=="__main__":
    parser=argparse.ArgumentParser();parser.add_argument("--root",type=pathlib.Path,default=pathlib.Path.cwd());parser.add_argument("--output",type=pathlib.Path,required=True)
    args=parser.parse_args(); data=inventory(args.root)
    args.output.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"modules":len(data["modules"]),"external_edges":len(data["external_edges"]),"sha256":sha(args.output.read_bytes())}))
