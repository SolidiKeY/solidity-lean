#!/usr/bin/env python3
"""Isolated serial config for the explicitly merged integration tree."""
from pathlib import Path
import re,subprocess,tomllib
root=Path(__file__).resolve().parents[4]
INTEGRATION="902e87762e5c3fb863bc3a592892f2dc09dfa979"
def main():
 original=subprocess.check_output(["git","show",INTEGRATION+":lakefile.toml"],cwd=root,text=True)
 assert (root/"lakefile.toml").read_text()==original
 parts=re.split(r"(?=^\[\[lean_(?:lib|exe)\]\])",original,flags=re.M)
 flags='weakLeanArgs = ["--tstack=131072", "-j1"]'
 for n,part in enumerate(parts):
  if not re.match(r"\[\[lean_(?:lib|exe)\]\]",part):continue
  if re.search(r"^weakLeanArgs\s*=",part,re.M):parts[n]=re.sub(r"^weakLeanArgs\s*=.*$",flags,part,flags=re.M)
  else:parts[n]=re.sub(r'^(name\s*=.*)$',lambda m:m[1]+"\n"+flags,part,count=1,flags=re.M)
 result="".join(parts)+'\n[[lean_lib]]\nname = "H62AbiWorld"\nsrcDir = "tests/h62/item2/audit-abi-world"\n'+flags+'\n'
 a=tomllib.loads(original);b=tomllib.loads(result)
 assert a["defaultTargets"]==b["defaultTargets"]
 for section in ("lean_lib","lean_exe"):
  assert len(b[section])==len(a[section])+(section=="lean_lib")
  for old,new in zip(a[section],b[section]):
   assert {k:v for k,v in old.items() if k!="weakLeanArgs"}=={k:v for k,v in new.items() if k!="weakLeanArgs"}
  for entry in b[section]:assert entry["weakLeanArgs"]==["--tstack=131072","-j1"]
 (root/"tests/h62/item2/audit-abi-world/resume-serial.lakefile.toml").write_text(result)
 print("Current integration defaults/targets preserved; explicit serial flags on every target")

if __name__=="__main__": main()
