#!/usr/bin/env python3
"""Reproduce H70 B05 without editing its live-owner original."""
import argparse, difflib, fcntl, hashlib, pathlib
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
if not a.check:
    lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
r=pathlib.Path(__file__).resolve().parents[4]
s=r/'Solidity/Yul/ReservedNames.lean';src=s.read_text()
assert hashlib.sha256(s.read_bytes()).hexdigest() == '723d2c323f67e8d0c4db6a4d0d0e2d267b9707d9bfaf9df3f502f9747dfed1b9'
old='theorem reservedNames_count : reservedNames.length = 157 := rfl'
new='theorem reservedNames_count : reservedNames.length = 157 := by decide +kernel'
assert src.count(old)==1
candidate=src.replace(old,new)
outputs={r/'tests/h62/item6/migrate-yul/ReservedNamesCandidate.lean':candidate+'\n#print axioms Solidity.Yul.reservedNames_count\n#print axioms Solidity.Yul.slotnum_not_reserved\n',
r/'tests/h62/item6/migrate-yul/ReservedNamesOriginalAxioms.lean':'import Solidity.Yul.ReservedNames\n#print axioms Solidity.Yul.reservedNames_count\n#print axioms Solidity.Yul.slotnum_not_reserved\n',
r/'scripts/h62/item6/migrate-yul/ReservedNames.proposed.patch':''.join(difflib.unified_diff(src.splitlines(True),candidate.splitlines(True),fromfile='a/Solidity/Yul/ReservedNames.lean',tofile='b/Solidity/Yul/ReservedNames.lean'))}
for path,text in outputs.items():
    if a.check:
        assert path.read_text()==text, str(path)+' differs'
    else:path.write_text(text)
print('B05 exact source/table/statements preserved; one kernel-proof replacement; fixture generation matches')
