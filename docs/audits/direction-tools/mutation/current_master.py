#!/usr/bin/env python3
"""Read-only source comparison; writes only its JSON deliverable. No mutation/execution."""
import argparse,hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
BASE="d4ad633a9624263a59b14fd2c520b9bc602f88f3"
def git(*args):return subprocess.check_output(["git",*args],cwd=ROOT)
def main():
 p=argparse.ArgumentParser();p.add_argument("--revision",required=True);a=p.parse_args()
 revision=git("rev-parse",a.revision+"^{commit}").decode().strip()
 assert git("merge-base",BASE,revision).decode().strip()==BASE
 mutants=json.loads((OUT/"mutants.json").read_text());rows=[]
 for m in mutants:
  before=git("show",BASE+":"+m["path"]);after=git("show",revision+":"+m["path"]);text=after.decode();count=text.count(m["old"])
  rows.append(dict(id=m["id"],path=m["path"],base_sha256=hashlib.sha256(before).hexdigest(),current_sha256=hashlib.sha256(after).hexdigest(),file_changed=before!=after,anchor_occurrences=count,current_line=text[:text.index(m["old"])].count("\n")+1 if count==1 else None,anchor_status="unique" if count==1 else "absent" if count==0 else "ambiguous"))
 result=dict(base=BASE,revision=revision,mutants=len(rows),rows=rows,boundary="Literal source-anchor drift only; no Lean name resolution, mutation application, theorem/test execution, timing or semantic inference.")
 (OUT/"current-master-drift.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
if __name__=="__main__":main()
