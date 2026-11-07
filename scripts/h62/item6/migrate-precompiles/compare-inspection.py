#!/usr/bin/env python3
"""Compare complete diagnostic logs; formatted type hashes are not kernel Expr hashes."""
import argparse,hashlib,json
from pathlib import Path
def parse(p):
    result={};sig=[]
    for line in p.read_text().splitlines():
        if line.startswith("'Solidity."):
            name=line.split("'")[1];typ=" ".join(" ".join(sig).split());sig=[]
            axs=line.split("axioms: ",1)[1][1:-1].split(", ") if "axioms:" in line else []
            if name in result:raise ValueError("duplicate declaration")
            result[name]=dict(type=typ,type_sha256=hashlib.sha256(typ.encode()).hexdigest(),axioms=axs)
        else:sig.append(line)
    if sig:raise ValueError("trailing messages; inspect incomplete or failed")
    return result
ap=argparse.ArgumentParser();ap.add_argument("old",type=Path);ap.add_argument("new",type=Path);a=ap.parse_args()
old=parse(a.old);new=parse(a.new)
result=dict(old_count=len(old),new_count=len(new),names_equal=old.keys()==new.keys(),
    type_changes=[n for n in old if n not in new or old[n]["type"]!=new[n]["type"]],
    axiom_changes=[dict(name=n,old=old[n]["axioms"],new=new[n]["axioms"]) for n in old if n in new and old[n]["axioms"]!=new[n]["axioms"]],
    old=old,new=new)
print(json.dumps(result,indent=2,sort_keys=True))
if not result["names_equal"] or result["type_changes"]:raise SystemExit(1)
