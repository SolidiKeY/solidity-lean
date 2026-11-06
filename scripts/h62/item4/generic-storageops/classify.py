#!/usr/bin/env python3
"""Source-contract classification of the entire frozen StorageOps inventory.

A row is a declaration/contract obligation, never a claimed independent test.
No source-equivalent declarations are merged. Proposition structure is recorded
without turning an observation's `none` into an operation refusal. Exact types,
parameters, local lets, bodies of fixtures and every source hash remain present.
This is an audit, not a Lean elaborator, proof or dependency graph.
"""
import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("census",HERE/"census.py")
c=importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
DOMAINS=c.ROOT/"tests/h62/item4/generic-storageops/semantic-domains.json"
MANIFEST=c.ROOT/"tests/h62/item4/generic-storageops/classification-manifest.json"
OPEN="([{⟨"
CLOSE=")] }⟩".replace(" ","")

def positions(text):
    """Positions outside explicit brackets, comments and strings."""
    code=c.mask(text,preserve_newlines=False); stack=[]
    for i,ch in enumerate(code):
        if ch in OPEN: stack.append(ch)
        elif ch in CLOSE:
            if stack: stack.pop()
        elif not stack and text[i]==ch: yield i

def top_splits(text,operator):
    starts=[i for i in positions(text) if text.startswith(operator,i)]
    if not starts: return None
    chunks=[]; last=0
    for i in starts:
        chunks.append(text[last:i].strip()); last=i+len(operator)
    chunks.append(text[last:].strip())
    return chunks

def unwrap(text):
    text=text.strip()
    while text.startswith("(") and text.endswith(")"):
        code=c.mask(text); depth=0; end=None
        for i,ch in enumerate(code):
            if ch=="(": depth+=1
            elif ch==")":
                depth-=1
                if depth==0: end=i; break
        if end!=len(text)-1: break
        text=text[1:-1].strip()
    return text

def expected_form(text):
    t=unwrap(text)
    if text.strip().startswith("(") and top_splits(t,","): return "product-expression"
    for pattern,label in [
        (r"^(?:Option\.)?none$|^\.none$","option-none"),
        (r"^(?:Option\.)?some\b|^\.some\b","option-some"),
        (r"^\.error\b","error-constructor"),
        (r"^\.revert\b","revert-constructor"),
        (r"^\.panic\b","panic-constructor"),
        (r"^\.refused\b","refused-constructor"),
        (r"^\.ok\b","ok-constructor"),
        (r"^(?:true|false)$","boolean-literal"),
        (r"^[0-9]+$","natural-literal"),
        (r"^\[","list-expression"),
    ]:
        if re.search(pattern,t): return label
    return "symbolic-expression"

def proposition(text):
    """Lossless shape tree. Leaves retain exact expressions; no boolean evaluation."""
    text=unwrap(text)
    if text.startswith(("∀","∃")):
        comma=next((i for i in positions(text) if text[i]==","),None)
        if comma is not None:
            return dict(form="forall" if text[0]=="∀" else "exists",
                binders=text[1:comma].strip(),body=proposition(text[comma+1:]))
    if re.match(r"let\b",text):
        places=list(positions(text))
        split=next((i for i in places if text[i]==";"),None)
        if split is None:
            code=c.mask(text); lines=code.splitlines()
            indents=[len(line)-len(line.lstrip()) for line in lines[1:] if line.strip()]
            base=min(indents) if indents else 0
            for i in places:
                if text[i]!="\n": continue
                rest=code[i+1:]; line=rest.split("\n",1)[0]
                if line.strip() and len(line)-len(line.lstrip())<=base:
                    split=i; break
        if split is None: raise ValueError("undelimited let proposition: "+text)
        return dict(form="let-proposition",binding=text[:split].strip(),body=proposition(text[split+1:]))
    # Lean implications bind more weakly than conjunction/equality.
    for op,label in [("↔","iff"),("→","implication"),("∨","disjunction"),("∧","conjunction")]:
        pieces=top_splits(text,op)
        if pieces: return dict(form=label,parts=[proposition(p) for p in pieces])
    if text.startswith("¬"):
        return dict(form="negation",body=proposition(text[1:]))
    for op,label in [("≠","inequality"),("≤","less-or-equal"),("≥","greater-or-equal"),("∉","not-member"),("∈","member")]:
        pieces=top_splits(text,op)
        if pieces and len(pieces)==2: return dict(form=label,left=pieces[0],right=pieces[1])
    for i in positions(text):
        if text[i]=="=" and (i==0 or text[i-1] not in "=:<>!") and text[i+1:i+2]!="=":
            return dict(form="equality",left=text[:i].strip(),right=text[i+1:].strip(),
                expected_form=expected_form(text[i+1:].strip()))
    if text in ("True","False"): return dict(form="truth" if text=="True" else "falsehood",expression=text)
    return dict(form="predicate-or-term-proposition",expression=text)

def declared_type(statement):
    for i in positions(statement):
        if statement[i]==":" and statement[i:i+2]!=":=":
            return statement[:i].rstrip(), statement[i+1:].strip()
    return statement,None

def walk(tree):
    yield tree
    if "body" in tree: yield from walk(tree["body"])
    for p in tree.get("parts",[]): yield from walk(p)

def assertions(tree, context="asserted", polarity=True):
    """Keep conditions, alternatives and equivalence sides out of asserted outcomes."""
    form=tree["form"]
    if form=="implication":
        for part in tree["parts"][:-1]: yield from assertions(part,"premise",polarity)
        yield from assertions(tree["parts"][-1],context,polarity)
    elif form=="iff":
        for part in tree["parts"]: yield from assertions(part,"equivalence-side",polarity)
    elif form=="disjunction":
        for part in tree["parts"]: yield from assertions(part,"alternative",polarity)
    elif form=="negation":
        yield dict(context=context,polarity=polarity,atom=tree)
        yield from assertions(tree["body"],context,not polarity)
    elif "parts" in tree:
        for part in tree["parts"]: yield from assertions(part,context,polarity)
    elif "body" in tree:
        yield from assertions(tree["body"],context,polarity)
    else: yield dict(context=context,polarity=polarity,atom=tree)

def equality_meaning(atom):
    """Narrow source-semantic labels; never deduce refusal from nested none."""
    lhs=atom["left"]; rhs=atom["right"]; expected=atom["expected_form"]
    if expected in ("list-expression","product-expression"):
        return "whole-ordered-value-or-observation-equality"
    if expected=="option-none":
        if re.search(r"\.(?:map|bind)\b",lhs): return "composed-partial-result-none"
        if "Solidity.Backend.StorageOps.Published." in lhs: return "published-fragment-refusal"
        if re.search(r"\.(?:readLive|find|observe)\b",lhs): return "unavailable-graph-observation"
        if re.search(r"\b(?:modifyAt|modifyMany|modifySlot|copyAt|pushAt|popAt|operationPush|recursivePop)\b|\.(?:push|pop)\b",lhs):
            return "partial-operation-no-returned-value"
        return "partial-result-none-exact-origin-retained"
    if expected=="option-some": return "partial-result-present-exact-payload-retained"
    if expected=="error-constructor": return "explicit-error-result"
    if expected=="revert-constructor": return "explicit-revert-result"
    if expected in ("ok-constructor","panic-constructor","refused-constructor"):
        return "explicit-"+expected.removesuffix("-constructor")+"-result"
    return "exact-value-or-relational-equality"

def contract_semantics(tree):
    entries=[]
    for entry in assertions(tree):
        atom=entry["atom"]
        item=dict(context=entry["context"],polarity=entry["polarity"],form=atom["form"])
        if atom["form"]=="equality": item["meaning"]=equality_meaning(atom)
        elif atom["form"]=="inequality": item["meaning"]="distinct-values-or-observations"
        elif atom["form"]=="negation": item["meaning"]="negated-exact-contract"
        elif atom["form"] in ("less-or-equal","greater-or-equal","member","not-member"):
            item["meaning"]="exact-bound-or-coverage-contract"
        elif atom["form"]=="predicate-or-term-proposition": item["meaning"]="named-or-term-defined-proposition"
        else: item["meaning"]="exact-"+atom["form"]+"-contract"
        item["contract"]=atom
        entries.append(item)
    return entries

def input_regime(parameters, ambient, result_type, tree):
    declared=bool(ambient or re.search(r"[({]\s*[^(){}]+\s*:",parameters))
    if declared: return "explicit-or-ambient-parameters"
    if tree and any(n["form"]=="forall" for n in walk(tree)):
        return "universal-result-parameters"
    if tree and any(n["form"]=="exists" for n in walk(tree)):
        return "existential-result-contract"
    if tree is None and result_type and "→" in result_type:
        return "function-or-dependent-result-type"
    return "no-declaration-or-ambient-parameters"

def role(row):
    if row["kind"] in ("theorem","lemma"):
        if row["control_file"]:
            return "private-control-claim" if row["private"] else "public-control-claim"
        return "family-proof-claim"
    if row["kind"] in ("structure","inductive"):
        return "interface-or-type-definition"
    if row["control_file"]: return "control-fixture-or-adapter"
    return "family-definition-or-adapter"

def audit_disposition(r):
    claim=r["kind"] in ("theorem","lemma")
    if r["kind"] in ("structure","inductive"):
        return {"9":"preserve-frozen-type-contract", "11":"no-helper-extraction-from-interface-fields", "16":"retain-interface-definition-outside-case-table"}
    if r["control_file"] and claim:
        return {"9":"retain-exact-contract-if-parameterized", "11":"retain-case-after-any-proved-shared-lemma-extraction", "16":"retain-one-whole-claim-row-with-all-conjuncts-and-observations"}
    if r["control_file"]:
        return {"9":"retain-typed-input-and-operation-adapter", "11":"shared-fixture-candidate-only-after-full-type-and-body-correspondence", "16":"typed-fixture-support-retain-definition-and-parameters"}
    if claim:
        return {"9":"existing-generic-or-supporting-law-preserve-parameters", "11":"shared-law-candidate-only-after-contract-correspondence", "16":"supporting-law-not-a-replacement-for-control-claims"}
    return {"9":"preserve-existing-operation-definition", "11":"no-unproved-helper-substitution", "16":"implementation-support-not-a-control-case"}

def classify():
    inventory=c.census()
    rendered=json.dumps(inventory,ensure_ascii=False,indent=2)+"\n"
    pins=json.loads(c.DEST.read_text())
    if c.digest(rendered)!=pins["inventory_sha256"]: raise ValueError("frozen inventory drift")
    domains=json.loads(DOMAINS.read_text())
    if domains["base"]!=c.BASE: raise ValueError("domain base differs")
    if set(domains["files"])!={Path(f["path"]).name for f in inventory["files"]}:
        raise ValueError("missing/extra module domain disposition")
    files=[]; declarations=[]; template_members={}
    by_file={}
    for row in inventory["declarations"]: by_file.setdefault(row["path"],[]).append(row)
    for f in inventory["files"]:
        source=(c.ROOT/f["path"]).read_text()
        code=c.mask(source); commands=list(c.COMMAND.finditer(code))
        offsets={source.count("\n",0,m.start())+1:(m.start(),commands[i+1].start() if i+1<len(commands) else len(code)) for i,m in enumerate(commands)}
        docs=re.search(r"/\-!([\s\S]*?)\-/",source)
        file_rows=[]
        for row in by_file.get(f["path"],[]):
            start,end=offsets[row["line"]]
            full=source[start:end].rstrip()
            if c.digest(full)!=row["declaration_sha256"]: raise ValueError("declaration boundary drift")
            params,result=declared_type(row["statement"])
            claim=row["kind"] in ("theorem","lemma")
            if claim and not result: raise ValueError("claim lacks explicit result: "+row["name"])
            previous=source[:start]
            comment=re.search(r"/\-\-((?:(?!/\-)[\s\S])*?)\-/\s*$",previous)
            tree=proposition(result) if claim else None
            item=dict(id=f["path"]+":"+str(row["line"]),path=f["path"],line=row["line"],name=row["name"],
                declaration_kind=row["kind"],private=row["private"],role=role(row),
                domain=domains["files"][Path(f["path"]).name]["domain"],
                formal_parameters=params,result_type=result,ambient_binders=row["ambient_binders"],
                statement=row["statement"],contract_shape=tree,
                source_doc=comment[1].strip() if comment else None,
                source_definition=None if claim else full,
                audit=audit_disposition(row),migration_status="retain-original-await-owner-and-proof",
                source_hashes={k:row[k] for k in ("header_sha256","statement_sha256","legacy_v1_statement_sha256","declaration_sha256")})
            # Outcome tags are structural only: option-none is not a refusal assertion.
            item["semantic_contracts"]=contract_semantics(tree) if tree else []
            item["conclusion_forms"]=dict(Counter(n["form"] for n in walk(tree))) if tree else {}
            item["equality_expected_forms"]=dict(Counter(n["expected_form"] for n in walk(tree) if n["form"]=="equality")) if tree else {}
            item["asserted_equalities"]=dict(Counter(a["meaning"] for a in item["semantic_contracts"] if a["context"]=="asserted" and a["polarity"] and a["form"]=="equality"))
            # Text templates identify actual repeated source, not equivalent resolved types.
            match=c.DECL.match(full)
            template=full[:match.start("name")]+"__declaration__"+full[match.end("name"):]
            template=template.strip()
            template_id=c.digest(template)
            item["source_template_sha256"]=template_id
            template_members.setdefault(template_id,[]).append(item["id"])
            item["input_regime"]=input_regime(params,row["ambient_binders"],result,tree)
            item["audit_evidence"]={
                "9":dict(category=item["input_regime"],evidence="formal_parameters, ambient_binders and all result quantifiers retained exactly",obligation="preserve-all-runtime-parameters-and-original-exact-contract"),
                "11":dict(category="source-template-candidate-pending-grouping",source_template_sha256=template_id,obligation="source-identity-does-not-prove-resolved-type-or-semantic-equivalence"),
                "16":dict(category="whole-control-claim" if row["candidate_case"] else "supporting-declaration",evidence="exact-contract-shape-and-fixture-definition",obligation="no-clause-observation-or-refusal-removed; no-finite-enumeration-substituted-for-runtime-parameters")}
            declarations.append(item); file_rows.append(item)
        files.append(dict(path=f["path"],sha256=f["sha256"],**domains["files"][Path(f["path"]).name],
            source_module_doc=docs[1].strip() if docs else None,
            roles=dict(Counter(r["role"] for r in file_rows)),declarations=len(file_rows)))
    repeats={k:v for k,v in template_members.items() if len(v)>1}
    for item in declarations:
        repeated=item["source_template_sha256"] in repeats
        item["audit_evidence"]["11"]["category"]="repeated-source-template-candidate" if repeated else "unique-source-template-retained"
        item["audit_evidence"]["11"]["instances"]=len(template_members[item["source_template_sha256"]])
    corrections=[dict(id=r["id"],name=r["name"],old=r["source_hashes"]["legacy_v1_statement_sha256"],corrected=r["source_hashes"]["statement_sha256"]) for r in declarations if r["source_hashes"]["statement_sha256"]!=r["source_hashes"]["legacy_v1_statement_sha256"]]
    totals=dict(files=len(files),declarations=len(declarations),roles=dict(Counter(r["role"] for r in declarations)),
        domains=dict(Counter(r["domain"] for r in declarations)),header_corrections=len(corrections),
        input_regimes=dict(Counter(r["input_regime"] for r in declarations)),
        repeated_source_template_groups=len(repeats),repeated_source_template_members=sum(map(len,repeats.values())),
        conclusion_forms=dict(sum((Counter(r["conclusion_forms"]) for r in declarations),Counter())),
        expected_forms=dict(sum((Counter(r["equality_expected_forms"]) for r in declarations),Counter())),
        asserted_equalities=dict(sum((Counter(r["asserted_equalities"]) for r in declarations),Counter())))
    return dict(format=1,base=c.BASE,inventory_sha256=pins["inventory_sha256"],
        policy="Source-contract classification; no declaration excluded, merged, proved or admitted. All1623 private/public control claim contracts retained, not a count of independent semantic tests. Shape tags do not infer refusal from absence or Source/bytecode correctness from lower-layer equations.",
        totals=totals,files=files,declarations=declarations,header_corrections=corrections,
        repeated_source_templates=repeats)

def validate(result, inventory):
    """Reject missing/duplicated/replaced rows, contracts or audit obligations."""
    expected={(r["path"],r["line"]):r for r in inventory["declarations"]}
    actual={(r["path"],r["line"]):r for r in result["declarations"]}
    if len(actual)!=len(result["declarations"]) or set(actual)!=set(expected):
        raise ValueError("classification row identity loss or duplication")
    if {r["path"] for r in result["files"]}!={f["path"] for f in inventory["files"]}:
        raise ValueError("classification file coverage loss")
    for key,r in actual.items():
        original=expected[key]
        for field in ("name","statement","ambient_binders"):
            if r[field]!=original[field]: raise ValueError("changed contract field "+field)
        if r["role"]!=role(original): raise ValueError("changed semantic role")
        for field,value in r["source_hashes"].items():
            if original[field]!=value: raise ValueError("changed source hash")
        if set(r["source_hashes"])!={"header_sha256","statement_sha256","legacy_v1_statement_sha256","declaration_sha256"}:
            raise ValueError("missing source hashes")
        if set(r["audit"])!={"9","11","16"} or set(r["audit_evidence"])!={"9","11","16"}:
            raise ValueError("lost audit disposition")
        if r["migration_status"]!="retain-original-await-owner-and-proof":
            raise ValueError("unapproved migration disposition")
    return True

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    if args.output.resolve().is_relative_to(c.ROOT): parser.error("bulk classification must stay outside git (H44)")
    result=classify(); validate(result,c.census()); rendered=json.dumps(result,ensure_ascii=False,indent=2)+"\n"
    pins=dict(format=1,base=c.BASE,inventory_sha256=result["inventory_sha256"],
        domains_sha256=c.digest(DOMAINS.read_text()),classification_sha256=c.digest(rendered),totals=result["totals"])
    manifest=json.dumps(pins,ensure_ascii=False,indent=2)+"\n"
    if args.write: MANIFEST.write_text(manifest)
    elif MANIFEST.read_text()!=manifest: raise SystemExit("FAIL: semantic classification drift")
    args.output.write_text(rendered)
    print(json.dumps(result["totals"],sort_keys=True))
    print("SOURCE_CONTRACT_CLASSIFICATION_PASS "+c.digest(rendered))
    print("Boundary: source classification only; no semantic correspondence/Lean/runtime gate claim.")

if __name__=="__main__": main()
