#!/usr/bin/env python3
"""H78 static consolidation of existing evidence only: never invokes Lean/Lake."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
AREA=Path("/workspace/h62-migrate-counterexamples");E=AREA/"evidence"
OUT=AREA/"retirement-h82/evidence";OUT.mkdir(parents=True,exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blocks(p):
 result={};name=None
 for line in p.read_text().splitlines():
  if line.removeprefix("@").startswith("Solidity.Counterexamples."):
   name=line.split(" :",1)[0].removeprefix("@");result[name]=[]
  elif line.startswith("'Solidity."):name=None
  if name is not None:result[name].append(line)
 return {name:"\n".join(lines)+"\n" for name,lines in result.items()}
oldp=E/"old-probes-2/FrozenInterfaces.log";newp=E/"new-probes/OverlapInterfaces.log"
old=blocks(oldp);new=blocks(newp);census=json.loads((E/"census.json").read_text())
assert len(old)==18 and len(new)==2
named=[];metadata=[]
for f in census["files"]:
 module=f["path"][:-5].replace("/",".")
 assert sha(ROOT/f["path"])==f["base_sha256"]
 for d in f["declarations"]:
  if d["name"]:
   name=module+"."+d["name"]
   named.append({"name":name,"kind_from_original_source":d["kind"],"source_path":f["path"],"source_line":d["line"],"source_sha256":f["base_sha256"],"visibility":"Source-default public; exact exported visibility not dumped", "old_signature":old[name],"new_signature":new.get(name),"signature_format":"Existing rendered #check text with universes/explicit/fullNames options; not a canonical export or structured binder-kind dump", "old_provenance":{"path":str(oldp),"sha256":sha(oldp)},"new_provenance":{"path":str(newp),"sha256":sha(newp)} if name in new else None,"shim_signature":None,"shim_implemented":False})
 for label in ("old-clean-2","new-clean-1"):
  p=AREA/label/".lake/build/lib/lean"/(module.replace(".","/")+".ilean")
  record={"module":module,"toolchain_run":label,"path":str(p),"available":p.is_file(),"complete_public_export":False}
  if p.is_file():
   x=json.loads(p.read_text());observed=[]
   for key,v in x["references"].items():
    try:c=json.loads(key).get("c",{})
    except ValueError:continue
    if c.get("m")==module:observed.append({"name":c.get("n"),"definition_range_zero_based":v.get("definition"),"visibility":None,"signature":None,"boundary":"Reference metadata only; not public/export certification"})
   record.update(sha256=sha(p),observed_reference_names=observed,decl_range_keys=sorted(x.get("decls",{})))
  metadata.append(record)
result={"source_base":census["base"],"status":"incomplete-existing-evidence-only","all_original_public_generated_declarations_inventoried":False,"named_old_count":len(old),"named_new_count":len(new),"named_records":named,"existing_ilean_metadata":metadata,"generated_families_requiring_full_export":["noConfusion","recOn","casesOn","match_ matchers","all other original public generated declarations"],"implemented_shims":[],"shim_records":[],"missing_evidence":["Complete old/new environment public exports with exact types, visibility, universes and binder order/kinds","Three unbuilt target modules","H78 public-api requirements file from root-gate VM"],"limits":"Do not classify missing generated records as absent, private or compatible. No Lean/Lake subprocess, no source edit, no blanket generated exclusion."}
(OUT/"api-existing-evidence.json").write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
print("Static existing-evidence consolidation:18 named old,2 named new;generated completeness UNKNOWN;shims0")
