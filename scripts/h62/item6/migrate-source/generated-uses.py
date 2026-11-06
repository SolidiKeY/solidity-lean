#!/usr/bin/env python3
"""Qualified/receiver generated-use candidates; not name resolution or Lean proof.
Usage: generated-uses.py CENSUS OUTPUT [ROOT]
Unqualified references and implicit tactic/elaborator uses are omitted.
This unchanged-tree audit does not implement adaptation-manifest validation.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent))
from census import mask

IDENT=r"[^\W\d][\w']*"
SUFFIX=r"(?:noConfusionType|noConfusion|recOn|casesOn|brecOn|rec|below|toCtorIdx|ctorIdx|match_[0-9]+|eq_[0-9]+|eq_def|injEq|inj|congr_simp)"
REFERENCE=re.compile(r"(?<![\w'.])(?:"+IDENT+r"\.)+"+SUFFIX+r"(?![\w'])")
DECL=re.compile(r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|opaque|inductive|structure|class)\s+([^\s{(:]+)")

def uses(text):
    result=[]; enclosing=None
    for number,line in enumerate(mask(text).splitlines(),1):
        m=DECL.match(line)
        if m: enclosing={"token":m.group(1),"line":number}
        for found in REFERENCE.finditer(line):
            # Declaration names are not use sites.
            if m and m.start(1)<=found.start()<m.end(1): continue
            result.append({"line":number,"column":found.start()+1,"token":found.group(),"enclosing_declaration_candidate":enclosing})
    return result

def main():
    c=json.loads(Path(sys.argv[1]).read_text());root=Path(sys.argv[3]) if len(sys.argv)>3 else Path.cwd()
    records=[]
    for f in c["files"]:
        data=(root/f["path"]).read_bytes()
        if hashlib.sha256(data).hexdigest()!=f["sha256"]: raise SystemExit("source differs from pinned census: "+f["path"])
        records += [{"path":f["path"],**u} for u in uses(data.decode())]
    changed=subprocess.check_output(["git","-C",str(root),"diff","--name-only",c["base"],"--","Solidity/Source"],text=True).splitlines()
    changed=sorted(set(changed) | set(subprocess.check_output(["git","-C",str(root),"ls-files","--others","--exclude-standard","--","Solidity/Source"],text=True).splitlines()))
    from collections import Counter
    result={"schema":1,"base":c["base"],"inspected_head":subprocess.check_output(["git","-C",str(root),"rev-parse","HEAD"],text=True).strip(),
      "policy":{"source":"H78 human correction","frozen":"authored statements, generated public API, and proof budgets","generated_signatures_frozen":True,"existing_users_must_remain_unchanged":True,"all_shims_must_be_listed":True},
      "boundary":"Lexical qualified/receiver candidates only; unqualified references and implicit uses omitted. Not elaborated name resolution or successful v4.35 validation. Preparatory unchanged-tree audit; no adaptation-manifest input supported.",
      "source_files_scanned":len(c["files"]),"candidate_count":len(records),"by_file":dict(sorted(Counter(r["path"] for r in records).items())),
      "source_files_changed":changed,"adapted_source_uses":[],"records":records,
      "remaining":"Target validation remains blocked by Hash/Raw dependencies and Source original-file coordination. Implicit generated eliminator/equation uses cannot be certified by this scan."}
    if changed: raise SystemExit("Source differences are rejected by this preparatory audit; implement/review an adapted-use manifest validator before auditing an adapted tree")
    Path(sys.argv[2]).write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"source_files_scanned":len(c["files"]),"candidate_count":len(records),"files_with_candidates":len(result["by_file"]),"adapted_source_uses":result["adapted_source_uses"]}))

if __name__=="__main__": main()
