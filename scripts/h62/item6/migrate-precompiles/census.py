#!/usr/bin/env python3
"""Deterministic source census; exact source hashes are stronger than API hashes.
Declaration/guard line indexes are navigational, not an elaborated API oracle.
"""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
from contract import expected
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
PREFIX = "Solidity/Precompiles/"
EXPECTED = sorted("Basic Blake2f Bls12381 Bls12381Iso Bn254 Field Modexp Osaka P256 Pairing PointEval".split())
def digest(b): return hashlib.sha256(b).hexdigest()
def imports(text): return re.findall(r"^import\s+(\S+)", text, re.M)
def census(root):
    files = sorted((root / PREFIX).glob("*.lean"))
    if [p.stem for p in files] != EXPECTED: raise ValueError("assigned module inventory changed")
    records = []
    for p in files:
        data = p.read_bytes(); text = data.decode(); rel = p.relative_to(root).as_posix()
        frozen = subprocess.check_output(["git", "show", BASE + ":" + rel], cwd=root)
        records.append(dict(path=rel, sha256=digest(data), base_sha256=digest(frozen),
            unchanged=data == frozen, migration_matches=data == expected(frozen,rel), bytes=len(data), lines=len(text.splitlines()),
            imports=imports(text),
            declarations=[dict(line=n, source=line.strip()) for n,line in enumerate(text.splitlines(),1)
                if re.match(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:def|theorem|lemma|structure|inductive|class|instance|abbrev)\b",line)],
            guards=[dict(line=n, source=line.strip()) for n,line in enumerate(text.splitlines(),1) if re.match(r"^#(?:guard_msgs|guard|eval|check|print)\b",line)],
            budgets=[dict(line=n, source=line.strip()) for n,line in enumerate(text.splitlines(),1) if "set_option" in line],
            trust_tokens=[dict(line=n, source=line.strip()) for n,line in enumerate(text.splitlines(),1)
                if re.search(r"\b(?:sorry|axiom|native_decide|debug\.skipKernelTC)\b",line)]))
    order=[]; visiting=set(); seen=set()
    def visit(m):
        if m in visiting: raise ValueError("cyclic import: " + m)
        if m in seen: return
        visiting.add(m); path=root / (m.replace(".","/") + ".lean")
        if not path.exists(): raise ValueError("external dependency: " + m)
        for dep in imports(path.read_text()): visit(dep)
        visiting.remove(m);seen.add(m);order.append(m)
    for p in files: visit(p.relative_to(root).with_suffix("").as_posix().replace("/","."))
    outside=[m for m in order if not m.startswith("Solidity.Precompiles.")]
    return dict(base=BASE, files=records, topological_closure=order, external_owner_modules=outside,
        external_sources=[dict(module=m,sha256=digest((root/(m.replace(".","/")+".lean")).read_bytes())) for m in outside],
        source_frozen=all(x["unchanged"] for x in records),
        migration_matches=all(x["migration_matches"] for x in records))
if __name__ == "__main__":
    ap=argparse.ArgumentParser();ap.add_argument("--root",type=Path,default=Path.cwd());ap.add_argument("--verify",action="store_true");ap.add_argument("--verify-migration",action="store_true");a=ap.parse_args()
    c=census(a.root.resolve());print(json.dumps(c,indent=2,sort_keys=True))
    if a.verify and not c["source_frozen"]: raise SystemExit(1)

    if a.verify_migration and not c["migration_matches"]: raise SystemExit(1)
