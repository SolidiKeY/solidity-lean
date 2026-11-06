#!/usr/bin/env python3
"""Compare explicit source declarations; retain complete compiler-generated API deltas."""
import argparse,hashlib,json,re
from pathlib import Path
from census import code_only,inventory

ANONYMOUS_INSTANCES = {
 ("Solidity.Syntax.Raw",448): "Solidity.instInhabitedContract",
 ("Solidity.Syntax.Elab.Context",902): "Solidity.instInhabitedSliceMRawExpr",
 ("Solidity.Syntax.Elab.Context",1344): "Solidity.instInhabitedForallUnitProg",
 ("Solidity.Syntax.Elab.Values",653): "Solidity.instInhabitedCallMemo",
 ("Solidity.Syntax.Elab.Lower",940): "Solidity.instCoeStringByteSrc",
 ("Solidity.Syntax.Elab.Arms",27): "Solidity.instInhabitedElabM",
 ("Solidity.Syntax.Elab.Stmt",26): "Solidity.instInhabitedElabM_1",
 ("Solidity.Syntax.Splice",152): "Solidity.instInContract",
}

def declarations(root):
 out=[]
 for file in inventory(root)["files"]:
  frames=[]
  for lineno,line in enumerate(code_only((root/file["path"]).read_text()).splitlines(),1):
   line=line.strip()
   scope=re.match(r"^(namespace|section|mutual)(?:\s+([^\s]+))?\s*$",line)
   if scope:
    frames.append((scope[1],scope[2] or ""));continue
   if re.match(r"^end(?:\s+\S+)?\s*$",line):
    if frames: frames.pop()
    continue
   m=re.match(r"^(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|local|scoped)\s+)*(def|theorem|lemma|inductive|structure|abbrev|class|instance|opaque)\s+([^\s(:{]+)",line)
   if not m:
    if re.match(r"^(?:local\s+|scoped\s+)?instance\b",line):
     key=(file["module"],lineno)
     if key not in ANONYMOUS_INSTANCES:raise ValueError("Unmapped original anonymous instance: "+str(key))
     out.append(dict(module=file["module"],name=ANONYMOUS_INSTANCES[key],kind="anonymous-instance",line=lineno,private=False,path=file["path"]))
    continue
   name=m[2]
   ns=".".join(n for k,n in frames if k=="namespace")
   fqn=(ns+"." if ns else "")+name
   out.append(dict(module=file["module"],name=fqn,kind=m[1],line=lineno,private=bool(re.search(r"\bprivate\b",line[:line.index(m[1])])),path=file["path"]))
 return out

def compare(root,oldrows,newrows,modules=None):
 if modules is not None and (not modules or not set(modules)<={r["module"] for r in inventory(root)["files"]}):raise ValueError("Explicit nonempty valid module subset required")
 old={r["name"]:r for r in oldrows};new={r["name"]:r for r in newrows}
 selected=[];missing=[];changed=[]
 for d in declarations(root):
  if modules is not None and d["module"] not in modules:continue
  names=[d["name"]] if not d["private"] else [n for n,r in old.items() if r["module"]==d["module"] and n.startswith("_private.") and n.endswith("."+d["name"])]
  if len(names)!=1 or names[0] not in old or names[0] not in new:
   missing.append(d);continue
  name=names[0];a=old[name];b=new[name]
  row=dict(source=d,elaborated_name=name,old=a,new=b)
  selected.append(row)
  if any(a[k]!=b[k] for k in ["name","module","type","universes"]):changed.append(row)
 delta=dict(removed=[old[n] for n in sorted(old.keys()-new.keys())],added=[new[n] for n in sorted(new.keys()-old.keys())],changed=[dict(old=old[n],new=new[n]) for n in sorted(old.keys()&new.keys()) if old[n]!=new[n]])
 axiom_additions=[dict(name=r["elaborated_name"],added=sorted(set(r["new"].get("axioms",[]))-set(r["old"].get("axioms",[])))) for r in selected if set(r["new"].get("axioms",[]))-set(r["old"].get("axioms",[]))]
 frozen=[{k:r["old"][k] for k in ["name","module","type","universes"]} for r in selected];encoded=json.dumps(sorted(frozen,key=lambda r:r["name"]),sort_keys=True,separators=(",",":"))
 return dict(status="pass" if not missing and not changed else "fail",source_declarations=len(selected),axiom_additions=axiom_additions,axiom_status="unchanged" if not axiom_additions else "root-gate-review-required",missing=missing,changed=changed,frozen_sha256=hashlib.sha256(encoded.encode()).hexdigest(),frozen=frozen,expected_declaration_modules=sorted({d["module"] for d in declarations(root) if modules is None or d["module"] in modules}),compiler_generated_and_other_delta=delta,note="Explicit named source declarations checked with canonical bound-variable types (binder labels/metadata erased; autoParam unfolded definitionally). Full generated/other declaration drift retained for root-gate audit, never silently accepted as unchanged.")
if __name__=="__main__":
 p=argparse.ArgumentParser();p.add_argument("--modules",nargs="+");p.add_argument("--root",type=Path,required=True);p.add_argument("old",type=Path);p.add_argument("new",type=Path);p.add_argument("--output",type=Path,required=True);a=p.parse_args();r=compare(a.root,json.loads(a.old.read_text()),json.loads(a.new.read_text()),a.modules);a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+"\n");print(json.dumps({k:r[k] for k in ["status","source_declarations","frozen_sha256"]}));print("missing",len(r["missing"]),"changed",len(r["changed"]));raise SystemExit(0 if r["status"]=="pass" else 1)
