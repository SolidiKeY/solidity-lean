#!/usr/bin/env python3
"""Reproduce isolated config with explicit -j1 for EVERY library/executable."""
from pathlib import Path
import re
import subprocess
import tomllib
root=Path(__file__).resolve().parents[4]
base="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
original=subprocess.check_output(["git","show",base+":lakefile.toml"],text=True,cwd=root)
parts=re.split(r"(?=^\[\[lean_(?:lib|exe)\]\])",original,flags=re.M)
flags='weakLeanArgs = ["--tstack=131072", "-j1"]'
for n,part in enumerate(parts):
 if not re.match(r"\[\[lean_(?:lib|exe)\]\]",part):continue
 if re.search(r"^weakLeanArgs\s*=",part,re.M):
  parts[n]=re.sub(r"^weakLeanArgs\s*=.*$",flags,part,flags=re.M)
 else:
  parts[n]=re.sub(r'^(name\s*=.*)$',lambda m:m[1]+"\n"+flags,part,count=1,flags=re.M)
result="".join(parts)+'''
# Isolated audit-only library; registration requires coordinator approval.
[[lean_lib]]
name = "H62AbiWorld"
srcDir = "tests/h62/item2/audit-abi-world"
weakLeanArgs = ["--tstack=131072", "-j1"]
'''
parsed=tomllib.loads(result);frozen=tomllib.loads(original)
assert parsed["defaultTargets"] == frozen["defaultTargets"]
for section in ("lean_lib","lean_exe"):
 for entry in parsed[section]:assert entry["weakLeanArgs"] == ["--tstack=131072","-j1"]
 for before,after in zip(frozen[section],parsed[section]):
  assert {k:v for k,v in before.items() if k!="weakLeanArgs"} == {k:v for k,v in after.items() if k!="weakLeanArgs"}
(root/"tests/h62/item2/audit-abi-world/serial.lakefile.toml").write_text(result)
print("All isolated library/executable targets have explicit -j1; frozen defaults unchanged")
