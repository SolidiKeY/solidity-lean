#!/usr/bin/env python3
"""Reuse the complete interface capture for a partial Parser/Annotations audit.
Generated capture source and printed interface output belong off git.
Text equality is evidence, not cross-version kernel equivalence.
"""
import argparse, hashlib, json, pathlib, re, sys
sys.dont_write_bytecode=True
from census import ROOT, census
p=argparse.ArgumentParser(); subs=p.add_subparsers(dest="mode",required=True)
s=subs.add_parser("source"); s.add_argument("out",type=pathlib.Path)
s=subs.add_parser("compat-source"); s.add_argument("out",type=pathlib.Path)
s=subs.add_parser("compare"); s.add_argument("old",type=pathlib.Path); s.add_argument("new",type=pathlib.Path)
a=p.parse_args()
if a.mode=="source":
    text=(ROOT/"tests/h62/item6/migrate-sortcheck/Interfaces.lean").read_text()
    assert text.count("import Solidity.SortCheck.Faithfulness\n")==1
    assert text.count(",\n    `Solidity.SortCheck.Faithfulness]")==1
    text=text.replace("import Solidity.SortCheck.Faithfulness\n", "").replace(",\n    `Solidity.SortCheck.Faithfulness]", "]")
    text=text.replace("Complete elaborated declaration census for all three imported modules", "Partial elaborated declaration census for Parser and Annotations")
    a.out.mkdir(parents=True)
    target=a.out/"ParserInterfaces.lean"; target.write_text(text)
    print(json.dumps({"path":str(target),"sha256":hashlib.sha256(target.read_bytes()).hexdigest()}))
elif a.mode=="compat-source":
    fragment="\nnamespace Solidity.TacletAnnotations\n"
    for name in ["ReadDomain","ReadSite","SortVarcond"]:
        fragment+=f'@[deprecated {name}.ctorIdx (since := "2025-08-25")]\nprotected abbrev {name}.toCtorIdx : {name} → Nat := {name}.ctorIdx\n'
    fragment+="end Solidity.TacletAnnotations\n"
    original=(ROOT/"tests/h62/item6/migrate-sortcheck/ConstructorTags.lean").read_text()
    text=original.replace("import Solidity.SortCheck.Annotations\n", "import Solidity.SortCheck.Annotations\n"+fragment,1)
    a.out.mkdir(parents=True)
    (a.out/"ConstructorTags.lean").write_text(text)
    (a.out/"annotations-compat.fragment.lean").write_text(fragment)
    print(json.dumps({"source":str(a.out/"ConstructorTags.lean"),"fragment_sha256":hashlib.sha256(fragment.encode()).hexdigest(),"boundary":"test-only proposal; no owner permission or production overlay inferred"}))
else:
    def declarations(path):
        text=path.read_text(); out={}
        for block in text.split("DECLARATION ")[1:]:
            name,body=block.split("\nTYPE ",1); ty,axioms=body.rsplit("\nAXIOMS ",1)
            assert name not in out,name
            out[name]={"type":" ".join(ty.split()),"axioms":sorted(set(re.findall(r"[A-Za-z_][A-Za-z_.]*",axioms)))}
        assert out, "no captured declarations"
        return out
    old=declarations(a.old); new=declarations(a.new)
    public=lambda n:not n.startswith("_private.") and not any(part.startswith("_") for part in n.split("."))
    required={n for n in old if public(n)}
    missing=sorted(required-new.keys())
    common=required&new.keys()
    changed_types=sorted(n for n in common if old[n]["type"]!=new[n]["type"])
    changed_axioms=sorted(n for n in common if old[n]["axioms"]!=new[n]["axioms"])
    source_api=set()
    for module,f in census()["files"].items():
        if module.endswith("Faithfulness"): continue
        prefix="Solidity.KeyTacletParser." if module.endswith("Parser") else "Solidity.TacletAnnotations."
        for command in f["commands"]:
            match=re.match(r"(?:def|abbrev|theorem|lemma|structure|inductive|class)\s+([\w.?]+)",command["text"])
            if match: source_api.add(prefix+match[1])
    unmatched_source_inventory=sorted(source_api-old.keys())
    if unmatched_source_inventory: raise ValueError("unmatched source-declared baseline API: "+repr(unmatched_source_inventory))
    assert source_api, "empty source API inventory"
    source_missing=sorted(source_api-new.keys())
    source_changed_types=sorted(n for n in source_api&new.keys() if old[n]["type"]!=new[n]["type"])
    result={"scope":"Parser and Annotations only; Faithfulness pending owner dependencies", "old_count":len(old),"new_count":len(new),"required_public_baseline_count":len(required),
      "missing_public":missing,"changed_public_printed_types":changed_types,"changed_public_axiom_sets":changed_axioms,
      "source_declared_api_count":len(source_api),"unmatched_source_inventory":unmatched_source_inventory,"missing_source_declared_api":source_missing,"changed_source_declared_printed_types":source_changed_types,"extra_new_names":sorted(new.keys()-old.keys()),
      "status":"pass" if not missing and not changed_types and not changed_axioms else "review-required", "boundary":"printed type/axiom comparison only; not cross-version definitional equality or full migration acceptance",
      "old_log_sha256":hashlib.sha256(a.old.read_bytes()).hexdigest(),"new_log_sha256":hashlib.sha256(a.new.read_bytes()).hexdigest()}
    print(json.dumps(result,indent=2)); raise SystemExit(result["status"]!="pass")
