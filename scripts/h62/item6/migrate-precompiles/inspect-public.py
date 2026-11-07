#!/usr/bin/env python3
"""Generate diagnostic checks for all source-named declarations except blocked Osaka.
Anonymous instances stay separately indexed in census; source hashes cover all bytes.
"""
import re
from pathlib import Path
root=Path.cwd();out=root/"tests/h62/item6/migrate-precompiles/Inspect.lean";out.parent.mkdir(parents=True,exist_ok=True)
lines=["import Solidity.Precompiles.PointEval", "import Solidity.Precompiles.P256", "import Solidity.Precompiles.Modexp", "import Solidity.Precompiles.Bn254", "import Solidity.Precompiles.Blake2f"]
for p in sorted((root/"Solidity/Precompiles").glob("*.lean")):
    if p.stem=="Osaka":continue
    stack=[]
    for line in p.read_text().splitlines():
        if line.startswith("namespace "):stack.append(line.split()[1]);continue
        if line.startswith("end "):stack.pop();continue
        m=re.match(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:def|theorem|lemma|structure|inductive|class|instance|abbrev)\s+([^\s:{(]+)",line)
        if not m or "private " in line or m[1]=="where":continue
        n=".".join(stack+[m[1]])
        lines += ["#check @"+n,"#print axioms "+n]
out.write_text("\n".join(lines)+"\n");print(out)
