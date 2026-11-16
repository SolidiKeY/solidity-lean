#!/usr/bin/env python3
"""Discrimination of existing literal vectors under recognized wide integer expressions.
python3 docs/audits/direction-tools/mutation/vector_projection.py --scratch BASE_WORKTREE
This is an arithmetic source projection, NOT Lean, DSL/interpreter, compiler or EVM execution.
"""
import argparse,hashlib,json,operator,re,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
from base_tree import BASE,ROOT,read_base_blobs
OUT=Path(__file__).resolve().parent
OPS="Solidity/Semantics/Ops.lean";VECTORS="Solidity/Examples/Tactics/ModularArithmetic.lean"
def main():
 ap=argparse.ArgumentParser();ap.add_argument("--scratch",type=Path,required=True);a=ap.parse_args();scratch=a.scratch.resolve();assert scratch!=ROOT
 assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=scratch,text=True).strip()==BASE
 assert not subprocess.check_output(["git","status","--porcelain"],cwd=scratch,text=True).strip()
 blobs=read_base_blobs([OPS,VECTORS]);original=blobs[OPS].decode();text=blobs[VECTORS].decode()
 begin=text.index("private def basic : Prog");end=text.index("\nexample : (Prog.run initial basic)",begin);block=text[begin:end]
 vectors=[]
 for m in re.finditer(r"assert\((addmod|mulmod)\((\d+), (\d+), (\d+)\) == (\d+)\);",block):
  x,y,k,expected=map(int,m.groups()[1:]);assert all(0<=v<2**256 for v in [x,y,k,expected]) and k>0
  vectors.append(dict(op=m[1],x=x,y=y,k=k,expected=expected,line=text[:begin+m.start()].count("\n")+1))
 assert len(vectors)==4
 guard="if k.val = 0 then none else PrimTy.uint.ofInt? (op.wide x.val y.val % k.val)";assert guard in original
 operations={"+":operator.add,"-":operator.sub,"*":operator.mul}
 def project(source):
  rules={}
  for name in ["addmod","mulmod"]:
   matches=re.findall(r"\| \."+name+r", x, y => x ([+*\-]) y",source);assert len(matches)==1;rules[name]=matches[0]
  rows=[]
  for v in vectors:
   actual=operations[rules[v["op"]]](v["x"],v["y"])%v["k"];assert 0<=actual<2**256
   rows.append(dict(**v,actual=actual,agrees=actual==v["expected"]))
  return dict(rules=rules,rows=rows,disagreements=sum(not r["agrees"] for r in rows))
 baseline=project(original);assert baseline["disagreements"]==0
 plans={m["id"]:m for m in json.loads((OUT/"mutants.json").read_text())};path=scratch/OPS;assert path.read_bytes()==blobs[OPS];results=[]
 for ident in ["M23","M24"]:
  m=plans[ident];assert m["path"]==OPS and original.count(m["old"])==1
  try:
   path.write_text(original.replace(m["old"],m["new"],1));r=project(path.read_text())
  finally:path.write_bytes(blobs[OPS])
  r.update(id=ident,outcome="literal-arithmetic-projection-discriminated" if r["disagreements"] else "literal-arithmetic-projection-undiscriminated");results.append(r)
 result=dict(base=BASE,source=VECTORS,source_sha256=hashlib.sha256(blobs[VECTORS]).hexdigest(),source_vectors=len(vectors),baseline=baseline,mutants=results,boundary="Exact existing basic literal assertions, positive uint256 operands/moduli, recognized unbounded integer +,-,* and positive remainder only. Tests whether these output vectors distinguish expressions; no Lean/DSL/interpreter execution, no project mutation kill or survival claim.")
 data=json.dumps(result,indent=2,sort_keys=True)+"\n";assert len(data.encode())<1000000;(OUT/"vector-projection.json").write_text(data)
 print(json.dumps({"base":BASE,"vectors":len(vectors),"outcomes":[{"id":r["id"],"outcome":r["outcome"],"disagreements":r["disagreements"]} for r in results],"new_Lean_elaborations":0},sort_keys=True))
if __name__=="__main__":main()
