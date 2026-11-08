#!/usr/bin/env python3
"""Verify saved probe source/log bindings without spending another Lean elaboration.
python3 docs/audits/direction-tools/mutation/verify_lean_probe.py --out EXTERNAL_DIR
"""
import argparse,hashlib,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
from base_tree import BASE,read_base_blobs
OUT=Path(__file__).resolve().parent

def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument("--out",type=Path,required=True);a=ap.parse_args()
 r=json.loads((OUT/"lean-probes.json").read_text());assert r["base"]==BASE and r["total_elaborations"]<=10
 ledger=json.loads((a.out/"attempts.json").read_text());assert len(ledger)==r["total_elaborations"]
 paths={x["path"] for x in r["source_slice_bindings"]}|{"Solidity/KeySort.lean","Solidity/Calculus/Closers.lean"}
 blobs=read_base_blobs(paths);parts=[]
 for item in r["source_slice_bindings"]:
  text=blobs[item["path"]].decode()
  if "text" in item:part=item["text"];assert text.count(part)==1
  else:
   assert text.count(item["start"])==1;begin=text.index(item["start"]);end=text.index(item["end"],begin+len(item["start"]));part=text[begin:end]
   assert text[:begin].count("\n")+1==item["line"]
  assert sha(part.encode())==item["sha256"];parts.append(part)
 fixture="import Lean\nnamespace Solidity\n"+"".join(x+("\n" if i==2 else "") for i,x in enumerate(parts))+"\nend Solidity\n"
 expected={"KeySort":blobs["Solidity/KeySort.lean"],"ClosersOriginal":blobs["Solidity/Calculus/Closers.lean"],"CloserSliceBaseline":fixture.encode(),"CloserSliceM31":fixture.replace("| .error .panic => true","| .error .panic => false",1).encode(),"CloserSliceM32":fixture.replace("| .error .exhausted => false","| .error .exhausted => true",1).encode()}
 for row in ledger:
  name=row["name"];assert Path(row.get("source_path",row["command"][-1])).read_bytes()==expected[name]
  assert sha(expected[name])==row["source_sha256"]
  log=Path(row["log"]).read_text();assert log[-5000:]==row["output"]
  assert "--as=12884901888" in row["command"] and "-j1" in row["command"]
 for row in [r["keysort"],r["original_module_baseline"],r["source_slice_baseline"]]+[m["probe"] for m in r["source_slice_mutants"]]:
  assert row in ledger
 assert r["keysort"]["returncode"]==0 and r["source_slice_baseline"]["returncode"]==0
 for m in r["source_slice_mutants"]:
  code=m["probe"]["returncode"];output=m["probe"]["output"]
  inferred="selected-source-slice-survived" if code==0 else "selected-source-slice-proof-failed" if code==1 and "unsolved goals" in output else "inconclusive"
  assert m["status"]==inferred
 counts={"proof_failed":sum(m["status"]=="selected-source-slice-proof-failed" for m in r["source_slice_mutants"]),"survived":sum(m["status"]=="selected-source-slice-survived" for m in r["source_slice_mutants"]),"inconclusive":sum(m["status"]=="inconclusive" for m in r["source_slice_mutants"])}
 assert r["source_slice_counts"]==counts
 print(json.dumps({"base":BASE,"verified_elaborations":len(ledger),"source_slice_counts":r["source_slice_counts"],"new_elaborations":0,"boundary":r["boundary"]},sort_keys=True))
if __name__=="__main__":main()
