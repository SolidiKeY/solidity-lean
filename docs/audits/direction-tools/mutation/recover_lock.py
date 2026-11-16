#!/usr/bin/env python3
"""Recover exact historical reference-lock bytes from Git history; no reconstruction/install/run.
python3 docs/audits/direction-tools/mutation/recover_lock.py
"""
import hashlib,json,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
from base_tree import BASE,ROOT
OUT=Path(__file__).resolve().parent
TARGET="e42c4cf3acece9d74a08ecbd41171b3c7b7c5494c39a87debcefecda9beff397"
PATH="tests/h62/item3/g52-differential/package-lock.json"
def git(*args):return subprocess.check_output(["git",*args],cwd=ROOT)
def main():
 candidates=[];matches=[]
 for row in git("rev-list","--objects",BASE,"--",PATH).decode().splitlines():
  oid,sep,path=row.partition(" ")
  if path!=PATH:continue
  data=git("cat-file","blob",oid);digest=hashlib.sha256(data).hexdigest();candidates.append(dict(git_blob=oid,sha256=digest,bytes=len(data)))
  if digest==TARGET:matches.append((oid,data))
 assert len(matches)==1,"exact historical lock not uniquely recovered"
 oid,data=matches[0];json.loads(data);commit=None
 for candidate in git("log",BASE,"--find-object="+oid,"--format=%H","--",PATH).decode().splitlines():
  if git("rev-parse",candidate+":"+PATH).decode().strip()==oid:commit=candidate;break
 assert commit is not None and git("show",commit+":"+PATH)==data
 (OUT/"historical-reference-lock.json").write_bytes(data)
 result=dict(history_base=BASE,historical_path=PATH,source_commit=commit,git_blob=oid,sha256=TARGET,bytes=len(data),candidates=candidates,status="exact-archived-bytes-recovered",environment_reproduction="NOT_REPLAYED",boundary="Exact Git blob hash matches captured report pin. No lock reconstruction, dependency installation, compiler/EVM execution or timing experiment performed.",citation="https://github.com/SolidiKeY/solidity-lean/blob/"+commit+"/"+PATH)
 (OUT/"reference-lock-recovery.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n");print(json.dumps(result,sort_keys=True))
if __name__=="__main__":main()
