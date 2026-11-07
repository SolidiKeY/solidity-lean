"""Deterministic import closure and exact source freeze; no elaborated API claim."""
import argparse, hashlib, json, re
from pathlib import Path

def sha(data):
    return hashlib.sha256(data).hexdigest()

def mask(text):
    # Preserve offsets/newlines; Lean comments nest, strings can escape quotes.
    out = list(text); i = 0; depth = 0; string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2; continue
            if text.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2; continue
            if text[i] != "\n": out[i] = " "
        elif string:
            if text[i] == "\\" and i+1 < len(text):
                out[i] = " "; i += 1; out[i] = " "
            elif text[i] == '"': out[i] = " "; string = False
            elif text[i] != "\n": out[i] = " "
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end == -1: end = len(text)
            out[i:end] = " " * (end-i); i = end; continue
        elif text.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2; continue
        elif text[i] == "'" and (char := re.match(r"'(?:\\.|[^'\\\n])'", text[i:])):
            end = i + len(char.group()); out[i:end] = " " * (end-i); i = end; continue
        elif text[i] == '"': out[i] = " "; string = True
        i += 1
    if depth or string: raise ValueError("unterminated comment/string")
    return "".join(out)

def imports(text):
    # Local tree uses one import command per line. Whitespace after import
    # may contain newlines; comments/strings are already masked.
    clean = mask(text)
    groups = re.findall(r"^[ \t]*(?:(?:public|meta)[ \t]+)*import\s+([^\n]+)", clean, re.M)
    result = []
    for group in groups:
        names = group.split()
        if not all(re.fullmatch(r"[\w]+(?:\.[\w]+)*", name) for name in names):
            raise ValueError("unsupported import syntax: " + group)
        result.extend(names)
    return result

def census(root):
    files = sorted(root.glob("Solidity/Evm/*.lean"))
    assigned = {str(p.relative_to(root).with_suffix("")).replace("/", ".") for p in files}
    records = {}; active = set(); order = []
    def visit(mod):
        if mod in active: raise ValueError("import cycle: " + mod)
        if mod in records: return
        path = root / (mod.replace(".", "/") + ".lean")
        if not path.is_file():
            if mod.split(".")[0] in {"Init", "Lean", "Std", "Lake"}: return
            raise ValueError("missing local import: " + mod)
        raw = path.read_bytes(); clean = mask(raw.decode())
        active.add(mod)
        deps = imports(raw.decode())
        for dep in deps: visit(dep)
        active.remove(mod)
        records[mod] = {"path": str(path.relative_to(root)), "sha256": sha(raw),
                        "imports": deps, "assigned": mod in assigned,
                        "declaration_keyword_count": len(re.findall(r"\b(?:theorem|lemma|def|abbrev|opaque|axiom|inductive|structure|class|instance)\b", clean)),
                        "sorry_tokens": len(re.findall(r"\bsorry\b", clean)),
                        "axiom_tokens": len(re.findall(r"\baxiom\b", clean)),
                        "budgets": [line.strip() for line in clean.splitlines() if "maxHeartbeats" in line or "maxRecDepth" in line]}
        order.append(mod)
    for mod in sorted(assigned): visit(mod)
    edges = sorted([mod,dep] for mod in assigned for dep in records[mod]["imports"] if dep not in assigned)
    return {"format": 1, "boundary": "Exact whole-source hashes freeze every declaration and proof; keyword counts are lexical only, not an elaborated declaration inventory.",
            "assigned_count": len(assigned), "closure_count": len(records), "external_edges": edges,
            "order": order, "modules": dict(sorted(records.items()))}

if __name__ == "__main__":
    p=argparse.ArgumentParser(); p.add_argument("root", type=Path); p.add_argument("output", type=Path)
    a=p.parse_args(); data=census(a.root); a.output.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
    print(json.dumps({k:data[k] for k in ("assigned_count","closure_count")}))
