#!/usr/bin/env python3
"""Evidence-specific SOURCE refinements for the remaining domain queue.

Does not change the generic classifier, resolve arbitrary opens/suffixes,
prove inhabitance, or compile owner overlays. Every original row remains.
"""
import argparse
import collections
import copy
import hashlib
import json
from pathlib import Path
import re
from census import BASE,generate,mask
from classify import frozen_sources,declaration_index,resolve,DECL,strip_outer

BASELINE_SHA256="319c69d844bbcafead40f35344e2a3d2300ca6afc0c2ad314dfa2fd0258241e7"

def sha(data):return hashlib.sha256(data).hexdigest()

def lexical_namespaces(source):
    clean=mask(source);stack=[];contexts={}
    for event in DECL.finditer(clean):
        kind,tail=event[1],event[2].strip()
        line=source.count("\n",0,event.start(1))+1
        contexts[line]=None if any(tag=="root-namespace-unresolved" for tag,_ in stack) else ".".join(name for tag,name in stack if tag=="namespace")
        if kind in ("namespace","section","mutual"):
            name=tail.split()[0] if tail else ""
            if kind=="namespace" and name.startswith("_root_."):
                # Rare root namespace blocks require more context than this
                # narrow pass; retain their declarations as unresolved.
                stack.append(("root-namespace-unresolved",name))
            else:stack.append((kind,name))
        elif kind=="end" and stack:stack.pop()
    return contexts

def fact(sources,path,excerpt,label):
    source=sources[path]
    if source.count(excerpt)!=1:raise ValueError("missing/ambiguous frozen fact: "+label)
    offset=source.index(excerpt)
    return {"label":label,"path":path,"line":source.count("\n",0,offset)+1,
            "file_sha256":sha(source.encode()),"excerpt":excerpt,"excerpt_sha256":sha(excerpt.encode())}

def primitive_scope(namespace,symbols,tails):
    hits=resolve("PrimTy",namespace,symbols,tails)
    return len(hits)==1 and hits[0]["name"]=="Solidity.PrimTy" and hits[0]["path"]=="Solidity/AST.lean"

def replacement(binder,bindings,namespace,symbols,tails,facts):
    if binder["domain"] is None:return None
    unresolved="unresolved" in binder["role"]
    domain=strip_outer(binder["domain"])
    family=resolve("Solidity.PrimTy.Denote","",symbols,tails)
    family_ok=len(family)==1 and family[0]["path"]=="Solidity/Semantics.lean" and family[0]["declared_result"].splitlines()[0].strip()=="PrimTy → Type"
    refs=[symbols[k] for k in binder["definition_evidence"]]
    closed=re.fullmatch(r"(?:Solidity\.)?PrimTy\.(bool|uint|int)\.Denote",domain)
    if closed and unresolved and family_ok:
        if "Solidity" in bindings or "PrimTy" in bindings or not primitive_scope(namespace,symbols,tails):return None
        constructor=closed[1]
        refs=[facts["constructors"]["label"],facts["denote"]["label"]]
        constraint="none in the Bool branch" if constructor=="bool" else f"PrimTy.{constructor}.inRange n = true"
        return {"role":"data-parameter" if constructor=="bool" else "refined-data-parameter",
                "basis":"exact constructor application of frozen PrimTy.Denote", "fact_labels":refs,
                "constructor":constructor,"carrier":"Bool" if constructor=="bool" else "Int",
                "constraint_source":constraint,"branch_sensitive":True}
    generic=re.fullmatch(r"([\w']+)\.Denote",domain)
    if generic and binder["role"]=="data-parameter" and family_ok and refs and {r["name"] for r in refs}=={"Solidity.PrimTy.Denote"} and generic[1] in bindings and primitive_scope(namespace,symbols,tails):
        receiver=bindings[generic[1]]
        if receiver["domain"] not in ("PrimTy","Solidity.PrimTy"):return None
        if "PrimTy" in bindings or "Solidity" in bindings:return None
        return {"role":"computed-data-parameter","basis":"receiver explicitly typed by the frozen PrimTy family",
                "receiver":generic[1],"receiver_domain":receiver["domain"],
                "fact_labels":[facts["constructors"]["label"],facts["denote"]["label"]],
                "branch_sensitive":True,"constraint_source":"bool: Bool; uint/int: inRange subtype; actual branch remains part of the joint witness"}
    if unresolved and domain in ("Address","ContractWorld.Address","Solidity.ContractWorld.Address") and domain.split(".")[0] not in bindings and refs and {r["name"] for r in refs}=={"Solidity.ContractWorld.Address"} and all(r["path"]=="Solidity/Semantics/ContractWorld.lean" for r in refs):
        return {"role":"refined-data-parameter","basis":"exact frozen ContractWorld.Address subtype and nested word alias",
                "fact_labels":[facts[k]["label"] for k in ("address","world-word","semantics-word","denote")],
                "constraint_source":"outer w.1 < (2:Int)^160; nested uint word inRange proof also retained",
                "carrier":"nested subtype of Int; not Roadmap.Address/Fin and not an unconstrained address"}
    if binder["role"]=="data-parameter" and (namespace=="Solidity.Language.FixedPoint" or namespace.startswith("Solidity.Language.FixedPoint.")) and re.fullmatch(r"(?:Solidity\.Language\.FixedPoint\.)?Fx\s+[\w']+",domain) and "Fx" not in bindings and domain.split()[0].split(".")[0] not in bindings:
        if refs and {r["name"] for r in refs}=={"Solidity.Language.FixedPoint.Fx"}:
            return {"role":"refined-data-parameter","basis":"explicit frozen Fx Type alias carries its own inRange proof",
                    "fact_labels":[facts["fx"]["label"]],"constraint_source":"t.inRange v = true", "carrier":"Int"}
    return None

def refine(report,sources,symbols,tails,facts):
    result=copy.deepcopy(report);changes=[]
    contexts={path:lexical_namespaces(sources[path]) for path in {r["path"] for r in result["declarations"]}}
    for row in result["declarations"]:
        namespace=contexts[row["path"]].get(row["line"])
        if namespace is None:continue
        bindings={}
        for group in ("section_context","explicit_and_leading_binders"):
            for number,binder in enumerate(row[group]):
                annotation=replacement(binder,bindings,namespace,symbols,tails,facts)
                if annotation:
                    before=binder["role"];binder["previous_source_role"]=before
                    binder["role"]=binder["sort"]=annotation["role"]
                    binder["source_refinement"]=annotation
                    binder["inhabitance"]="not-established; refinements and all other arguments still require a simultaneous witness"
                    changes.append({"source_id":row["source_id"],"group":group,"ordinal":number,
                                    "binder":binder["name"],"domain":binder["domain"],"before":before,
                                    "after":annotation["role"],"evidence":annotation})
                bindings[binder["name"]]=binder
        relevant=[b for b in row["section_context"] if b["activation"]=="referenced-dependency-closure"]+row["explicit_and_leading_binders"]
        row["role_counts"]=dict(sorted(collections.Counter(b["role"] for b in relevant).items()))
        unresolved=any("unresolved" in b["role"] for b in relevant)
        row["source_sort_resolution"]="contains-unresolved-domains" if unresolved else "all-header-and-referenced-context-domains-source-classified"
        row["remaining_pass_boundary"]="Evidence-specific source classification only; no active-open inference, semantic telescope or inhabitance claim"
    result["summary"]["source_sort_resolution"]=dict(collections.Counter(r["source_sort_resolution"] for r in result["declarations"]))
    result["summary"]["semantic_classification_complete"]=False;result["summary"]["new_witness_claims"]=0
    return result,changes

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--baseline",type=Path,required=True);p.add_argument("--census",type=Path,required=True);p.add_argument("--output",type=Path,required=True);args=p.parse_args()
    if args.output.resolve().is_relative_to(Path(__file__).resolve().parents[4]):raise ValueError("bulk evidence must be outside repository")
    payload=args.baseline.read_bytes()
    if sha(payload)!=BASELINE_SHA256:raise ValueError("baseline source classification differs from reviewed checkpoint")
    census=json.loads(args.census.read_text())
    if census!=generate():raise ValueError("census differs from frozen source or pinned ownership")
    baseline=json.loads(payload);sources=frozen_sources()
    facts={
      "constructors":fact(sources,"Solidity/AST.lean","inductive PrimTy where\n  | bool\n  | uint\n  | int", "PrimTy-constructors"),
      "denote":fact(sources,"Solidity/Semantics.lean","def PrimTy.Denote : PrimTy → Type\n  | .bool => Bool\n  | .uint => {n : Int // PrimTy.uint.inRange n = true}\n  | .int => {n : Int // PrimTy.int.inRange n = true}","PrimTy-Denote-branches"),
      "address":fact(sources,"Solidity/Semantics/ContractWorld.lean","abbrev Address := { w : Word // w.1 < (2 : Int) ^ 160 }","ContractWorld-Address-refinement"),
      "world-word":fact(sources,"Solidity/Semantics/ContractWorld.lean","abbrev Word := Semantics.Word","ContractWorld-Word-alias"),
      "semantics-word":fact(sources,"Solidity/Semantics.lean","abbrev Word := PrimTy.uint.Denote","Semantics-Word-alias"),
      "fx":fact(sources,"Solidity/Language/FixedPoint.lean","def Fx (t : FxTy) : Type := {v : Int // t.inRange v = true}","FixedPoint-Fx-refinement")}
    symbols,tails=declaration_index(sources)
    result,changes=refine(baseline,sources,symbols,tails,facts)
    original_ids=[r["id"] for r in census["declarations"]];new_ids=[r["source_id"] for r in result["declarations"]]
    if new_ids!=original_ids or len(set(new_ids))!=len(new_ids):raise ValueError("source census changed")
    for before,after in zip(baseline["declarations"],result["declarations"]):
        if before["signature_sha256"]!=after["signature_sha256"] or before["owner"]!=after["owner"] or not after["in_scope"] or after["exclusion"] is not None:raise ValueError("frozen statement/owner/exclusion changed")
    result["remaining_pass"]={"baseline_sha256":BASELINE_SHA256,"generator_sha256":sha(Path(__file__).read_bytes()),"facts":facts,"changes":changes,"new_witnesses":0,"semantic_classification_complete":False}
    args.output.mkdir(parents=True,exist_ok=True)
    raw=(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n").encode()
    (args.output/"classification.json").write_bytes(raw);(args.output/"classification.sha256").write_text(sha(raw)+"  classification.json\n")
    pending=[r for r in result["declarations"] if r["source_sort_resolution"]=="contains-unresolved-domains"]
    (args.output/"unresolved-domains.json").write_text(json.dumps(pending,indent=2,ensure_ascii=False)+"\n")
    summary={"source_candidates":len(new_ids),"binder_refinements":len(changes),"resolved_unknown_binders":sum("unresolved" in c["before"] for c in changes),"enriched_data_binders":sum("unresolved" not in c["before"] for c in changes),"affected_rows":len({c["source_id"] for c in changes}),"remaining_unresolved_rows":len(pending),"new_witnesses":0,"semantic_classification_complete":False}
    (args.output/"summary.json").write_text(json.dumps(summary,indent=2)+"\n");print(json.dumps(summary,sort_keys=True))

if __name__=="__main__":main()
