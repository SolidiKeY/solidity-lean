#!/usr/bin/env python3
"""Inventory declarations at the pinned source; never rewrites owner files."""
import hashlib, json, pathlib, re, subprocess
root = pathlib.Path(__file__).resolve().parents[3]
records=[]
for file in sorted((root/'Solidity/Yul/Compilation').glob('*.lean')):
    data=file.read_bytes()
    source=data.decode()
    for match in re.finditer(r'^(structure|inductive) (Artifact|Compiled)\b[^\n]*',source,re.M):
        records.append(dict(path=str(file.relative_to(root)),line=source[:match.start()].count('\n')+1,
            declaration=match.group(),sha256=hashlib.sha256(data).hexdigest()))
print(json.dumps(dict(head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
    definitions=len(records),files=len({x['path'] for x in records}),declarations=records),indent=2))
assert len(records)==38 and len({x['path'] for x in records})==23
