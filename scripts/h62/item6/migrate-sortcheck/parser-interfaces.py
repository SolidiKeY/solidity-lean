#!/usr/bin/env python3
"""Reuse the complete interface capture for a partial Parser/Annotations audit.
Generated capture source and printed interface output belong off git.
Text equality is evidence, not cross-version kernel equivalence.
"""
import argparse, hashlib, json, pathlib, re, sys
sys.dont_write_bytecode=True
from census import ROOT, census
from migration import alias_block
p=argparse.ArgumentParser(); subs=p.add_subparsers(dest="mode",required=True)
s=subs.add_parser("source"); s.add_argument("out",type=pathlib.Path)
s=subs.add_parser("compat-source"); s.add_argument("out",type=pathlib.Path); s.add_argument("--inject-base-aliases",action="store_true",help="historical vanilla435 Annotations artifacts only")
s=subs.add_parser("compare"); s.add_argument("old",type=pathlib.Path); s.add_argument("new",type=pathlib.Path)
s=subs.add_parser("canonical-compare"); s.add_argument("old",type=pathlib.Path); s.add_argument("new",type=pathlib.Path); s.add_argument("--full-baseline-axioms",type=pathlib.Path)
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
    fragment="\nnamespace Solidity.TacletAnnotations\n"+alias_block()+"end Solidity.TacletAnnotations\n"
    original=(ROOT/"tests/h62/item6/migrate-sortcheck/ConstructorTags.lean").read_text()
    text=original.replace("import Solidity.SortCheck.Annotations\n", "import Solidity.SortCheck.Annotations\n"+fragment,1) if a.inject_base_aliases else original
    a.out.mkdir(parents=True)
    (a.out/"ConstructorTags.lean").write_text(text)
    (a.out/"annotations-compat.fragment.lean").write_text(fragment)
    print(json.dumps({"source":str(a.out/"ConstructorTags.lean"),"fragment_sha256":hashlib.sha256(fragment.encode()).hexdigest(),"boundary":"test-only proposal; no owner permission or production overlay inferred"}))
elif a.mode=="canonical-compare":
    def canonical(path):
        out={}; lines=path.read_text().splitlines()
        counts=[line[len("CANONICAL_COUNT "):] for line in lines if line.startswith("CANONICAL_COUNT ")]
        assert len(counts)==1 and counts[0].isdigit() and int(counts[0])>0,"missing/invalid/duplicate declared census count"
        for line in lines:
            if not line.startswith("CANONICAL "): continue
            name,universes,ty,axioms,binder_names=json.loads(line[len("CANONICAL "):])
            assert isinstance(name,str) and name and type(universes) is int and universes>=0
            assert isinstance(axioms,list) and all(isinstance(x,str) for x in axioms)
            assert isinstance(binder_names,list)
            assert name not in out,name
            def validate(node):
                if not isinstance(node,list): return
                if node and node[0]=="param":
                    assert len(node)==2 and isinstance(node[1],int) and 0<=node[1]<universes,"undeclared universe parameter"
                for child in node: validate(child)
            validate(ty)
            out[name]={"universes":universes,"type":ty,"axioms":sorted(set(axioms)),"binder_names":binder_names}
        assert len(out)==int(counts[0]),"truncated or inconsistent canonical census"
        assert "unexpected-" not in json.dumps(out),"unexpected open type node"
        return out
    old=canonical(a.old); new=canonical(a.new)
    public=lambda n:not n.startswith("_private.") and not any(part.startswith("_") for part in n.split("."))
    required={n for n in old if public(n)}
    common=required&new.keys()
    missing=sorted(required-new.keys())
    changed_types=sorted(n for n in common if old[n]["universes"]!=new[n]["universes"] or old[n]["type"]!=new[n]["type"])
    changed_axioms=sorted(n for n in common if old[n]["axioms"]!=new[n]["axioms"])
    changed_binder_names=sorted(n for n in common if old[n]["binder_names"]!=new[n]["binder_names"])
    binder_only={}; other_type_changes=[]
    for name in changed_types:
        changes=[]; other=[]
        def differences(a,b,path):
            if a==b: return
            if not isinstance(a,list) or not isinstance(b,list) or len(a)!=len(b):
                other.append(path); return
            is_binder=bool(a) and a[0]==b[0] and a[0] in ["forall","lam"]
            for i,(left,right) in enumerate(zip(a,b)):
                if is_binder and i==1 and left!=right:
                    changes.append({"path":path+[i],"old_binder_info":left,"new_binder_info":right})
                else: differences(left,right,path+[i])
        differences(old[name]["type"],new[name]["type"],[])
        if old[name]["universes"]!=new[name]["universes"]: other.append(["universe_arity"])
        if other: other_type_changes.append({"name":name,"paths":other})
        else: binder_only[name]=changes
    old_union=sorted({x for v in old.values() for x in v["axioms"]})
    new_union=sorted({x for v in new.values() for x in v["axioms"]})
    full_union=None; full_hash=None
    if a.full_baseline_axioms:
        baseline_text=a.full_baseline_axioms.read_text()
        assert hashlib.sha256(a.full_baseline_axioms.read_bytes()).hexdigest()=="85430e37388519d87672f7bd40ae3f12af7f66190f13011b064dd3d7e7cc818a","full baseline hash mismatch"
        assert baseline_text.startswith("DECLARATION_COUNT 658\n"),"wrong full baseline census"
        full_union=sorted({axiom for line in baseline_text.splitlines() if line.startswith("AXIOMS ")
          for axiom in re.findall(r"[A-Za-z_][A-Za-z_.]*",line[len("AXIOMS "):])})
        full_hash=hashlib.sha256(a.full_baseline_axioms.read_bytes()).hexdigest()
    result={"scope":"Parser/Annotations only", "old_count":len(old),"new_count":len(new),"baseline_public_count":len(required),
      "missing_public":missing,"changed_alpha_structural_types":changed_types,"changed_public_axiom_sets":changed_axioms,
      "axiom_deltas":{n:{"old":old[n]["axioms"],"new":new[n]["axioms"],"added_dependencies":sorted(set(new[n]["axioms"])-set(old[n]["axioms"]))} for n in changed_axioms},
      "changed_binder_name_maps":changed_binder_names,
      "binder_name_deltas":{n:{"old":old[n]["binder_names"],"new":new[n]["binder_names"]} for n in changed_binder_names},
      "binder_info_only_changes":binder_only,"other_type_changes":other_type_changes,
      "logical_structure_status":"pass" if not missing and not other_type_changes else "review-required",
      "binder_info_codes":{"0":"explicit","1":"implicit","2":"strictImplicit","3":"instImplicit"},
      "classification":"Binder-only changes preserve quantified domains/bodies but can affect positional call elaboration; not silently accepted as a frozen API waiver.",
      "old_axiom_union":old_union,"new_axiom_union":new_union,
      "full_old_SortCheck_axiom_union":full_union,"full_old_baseline_sha256":full_hash,
      "introduced_vs_full_old_SortCheck":sorted(set(new_union)-set(full_union)) if full_union is not None else None,"introduced_axiom_primitives":sorted(set(new_union)-set(old_union)),
      "type_status":"pass" if not missing and not changed_types else "review-required",
      "status":"pass" if not missing and not changed_types and not changed_axioms and not changed_binder_names else "review-required",
      "boundary":"Binder names can affect named-argument calls; normalized logical structure is not frozen elaborator API acceptance. Structural type audit erases binder names/type metadata and numbers universe parameters; not cross-version kernel equivalence or full migration acceptance",
      "old_log_sha256":hashlib.sha256(a.old.read_bytes()).hexdigest(),"new_log_sha256":hashlib.sha256(a.new.read_bytes()).hexdigest()}
    print(json.dumps(result,indent=2)); raise SystemExit(result["status"]!="pass")
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
