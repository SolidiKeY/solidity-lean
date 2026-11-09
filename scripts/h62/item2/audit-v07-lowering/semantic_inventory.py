#!/usr/bin/env python3
"""Source-evidenced premise roles for every frozen mapped theorem header.

Disambiguates propositions from data/functions without elaboration. Ambiguous
constants, inherited telescope membership and result-type inputs stay pending.
Neither Type-valued records nor Prop-valued assumptions are assumed inhabited.
"""
import argparse
import collections
import hashlib
import json
import pathlib
import re
from census import masked
from source_inventory import PAIRS, CLOSE, binders, terminator, context, classification


def top_positions(text):
    stack = []
    for i, c in enumerate(text):
        if not stack:
            yield i, c
        if c in PAIRS:
            stack.append(PAIRS[c])
        elif c in CLOSE:
            if not stack or stack.pop() != c:
                raise ValueError("unbalanced type expression")
    if stack:
        raise ValueError("unclosed type expression")


def strip_outer(text):
    text = masked(text).strip()
    while text.startswith("(") and text.endswith(")"):
        if list(top_positions(text)) != [(0, "(")]:
            break
        text = text[1:-1].strip()
    return text


def classify(domain, prior_category, relation_names=None, type_names=()):
    relation_names = relation_names or {}
    if domain is None:
        return "unresolved", "binder has no explicit type"
    text = strip_outer(domain)
    top = list(top_positions(text))
    if text in type_names:
        return "data-input", "caller-declared abstract type; no inhabitant inferred"
    if text == "Prop":
        return "proposition-parameter", "Prop is a universe; a value of Prop is a proposition parameter, not its proof"
    if re.fullmatch(r"(?:Type|Sort)(?:\s+.+)?", text):
        return "type-parameter", "universe parameter; no Nonempty premise follows"
    if text.startswith("∀"):
        commas = [i for i, c in top if c == ","]
        if not commas:
            return "unresolved", "unparsed universal telescope"
        kind, reason = classify(text[commas[0]+1:], "unresolved", relation_names, type_names)
        if kind == "proof-assumption":
            return kind, "universal proof obligation; "+reason
        if kind in ("proposition-parameter", "predicate-family"):
            return "predicate-family", "dependent family returning propositions, not a proof"
        if kind in ("data-input", "data-function"):
            return "data-function", "dependent function with data codomain"
        return "unresolved", "universal codomain unresolved: "+reason
    arrows = [i for i, c in top if c == "→"]
    if arrows:
        kind, reason = classify(text[arrows[-1]+1:], "unresolved", relation_names, type_names)
        if kind == "proof-assumption":
            return kind, "implication/function ending in a proposition; "+reason
        if kind in ("proposition-parameter", "predicate-family"):
            return "predicate-family", "function returning Prop (or a predicate family), not an assumed proof"
        if kind in ("data-input", "data-function", "global-contract", "indexed-certificate"):
            return "data-function", "function returning data/certificate; inhabitance is separate"
        return "unresolved", "arrow codomain unresolved: "+reason
    if text.startswith(("∃", "¬")) or text in ("True", "False"):
        return "proof-assumption", "existential/negation/True/False proposition constructor"
    if any(c in "=≠≤≥<>∧∨↔∈" for _, c in top):
        return "proof-assumption", "top-level equality, order, membership or logical proposition operator"
    if text.startswith(("Nonempty ", "Function.Injective ", "Function.Surjective ")):
        return "proof-assumption", "standard proposition-valued predicate"
    if re.match(r"(?:[A-Za-z0-9_.]+\.)?IntegerLocalFamily(?:\s|$)",text):
        return "proof-assumption", "IntegerLocalFamily source structure is explicitly declared : Prop where; full header fact recorded"
    if prior_category.startswith("global-"):
        return "global-contract", "global specification/reference/producer record; all fields must coexist"
    if prior_category in ("indexed-certificate-or-map", "request-contract-candidate", "producer-dependent-certificate"):
        return "indexed-certificate", "request/context/environment-indexed record or map; not a successful run"
    if prior_category in ("environment-support-predicate", "per-input-predicate-candidate"):
        return "proof-assumption", "source-declared support/relation/range predicate; source constant resolution still pending"
    if prior_category == "relation-parameter":
        return "predicate-family", "P12 alias is a function ending in Prop; not a proof of alignment"
    head = re.match(r"([^\s(]+)", text)
    if head and head[1] in relation_names:
        args = len([part for part in split_atoms(text) if part])-1
        arity = relation_names[head[1]]
        if args == arity:
            return "proof-assumption", "caller-declared predicate family applied to its source-declared argument count; elaboration still pending"
        if args < arity:
            return "predicate-family", "partially applied predicate family; not an assumed proof"
        return "unresolved", "predicate application exceeds source-declared argument count"
    if head and head[1].rsplit(".", 1)[-1] in {"AddressRel", "EnumRel", "Rel", "Supported", "Aligned"}:
        return "proof-assumption", "matching mapped declaration has Prop codomain; exact source headers recorded, constant resolution pending"
    if re.search(r"(?:^|\.)(?:Related|GraphTypeRel|GraphFieldsRel)(?:\s|$)", text):
        return "proof-assumption", "mapped source declares this correspondence as Prop; resolution pending"
    if prior_category in ("data-or-index-candidate", "abstract-type-data"):
        return "data-input", "source-declared data/index carrier; may itself be empty"
    # Atomic tails of function types can be recognized independently of the
    # outer syntactic category; never search for data names inside predicates.
    if re.match(r"(?:Nat|Int|Bool|String|Name|Fin|List|Option|Idx|TEnv|Out|Source\.(?:Idx|DeclName)|[A-Za-z_][A-Za-z0-9_.]*\.(?:Denote|TDenote))(?:\s|$)", text):
        return "data-input", "recognized data codomain"
    return "unresolved", "source expression needs name/type resolution; not defaulted to a feasible premise"


def role(domain, kind, prior_category):
    if kind == "global-contract":
        return "global-premise-record"
    if kind == "indexed-certificate":
        return "indexed-certificate-not-execution"
    if kind in ("proposition-parameter", "type-parameter", "predicate-family"):
        return "specification-parameter"
    if kind in ("data-input", "data-function"):
        return "input-or-index-needing-inhabitant"
    if kind == "proof-assumption":
        if "IntegerLocalFamily" in domain:
            return "per-input-family-alignment"
        if prior_category == "environment-support-predicate":
            return "environment-support-feasibility"
        if re.search(r"\.run\b|evalE|evalPair", domain):
            return "per-input-execution-feasibility"
        if "frontend" in domain:
            return "per-input-admission-feasibility"
        return "per-input-or-universal-proof-obligation"
    return "unresolved"


def split_atoms(text):
    starts = []
    start = 0
    for i, c in top_positions(text):
        if c.isspace():
            if text[start:i].strip():
                starts.append(text[start:i].strip())
            start = i+1
    if text[start:].strip():
        starts.append(text[start:].strip())
    return starts


def classify_binders(groups, aliases=None):
    rows = []
    relation_names = dict(aliases or {})
    type_names = set()
    for index, b in enumerate(groups):
        kind, reason = classify(b["domain_source"], b["category"], relation_names, type_names)
        if kind == "predicate-family":
            names = b["source"][1:].split(":", 1)[0].split()
            domain = strip_outer(b["domain_source"])
            arity = sum(c == "→" for _,c in top_positions(domain))
            if b["category"] == "relation-parameter":
                arity = 6 if domain.startswith("ValueRelation ") else 2
            relation_names.update((name,arity) for name in names)
        if kind == "type-parameter":
            type_names.update(b["source"][1:].split(":",1)[0].split())
        rows.append(dict(index=index, source=b["source"], domain_source=b["domain_source"],
            prior_category=b["category"], kind=kind, role=role(b["domain_source"] or "",kind,b["category"]),
            reason=reason, semantic_status="source-evidence; pending elaboration", inhabitation="unproved"))
    return rows


def predicate_facts(repo, modules):
    result = []
    for module in modules:
        source = (repo/module["path"]).read_text()
        code = masked(source)
        for m in re.finditer(r"^def (AddressRel|EnumRel|Rel|Supported|Aligned)\b", code,re.M):
            end, term = terminator(code,m.end())
            header = source[m.start():end]
            if not re.search(r"(?:→|:)\s*Prop\s*$",masked(header)):
                raise ValueError("predicate does not declare Prop codomain: "+header)
            ns,_ = context(source,code,m.start())
            result.append(dict(name=ns+"."+m[1],path=module["path"],start=m.start(),end=end,
                header_source=header,header_sha256=hashlib.sha256(header.encode()).hexdigest(),
                module_sha256=module["sha256"],evidence="source-declared Prop codomain, not elaborated resolution"))
    assert {f["name"].rsplit(".",1)[-1] for f in result} == {"AddressRel","EnumRel","Rel","Supported","Aligned"}
    return result


def result_inputs(row):
    signature = row["signature_source"]
    m = re.match(r"(?:theorem|lemma)\s+[^\s({\[:]+", signature)
    pos = m.end()
    for group in row["binder_evidence"]:
        pos += len(signature[pos:])-len(signature[pos:].lstrip())
        assert signature.startswith(group["source"],pos)
        pos += len(group["source"])
    tail = signature[pos:].lstrip()
    assert tail.startswith(":"),row["source_qualified_name"]
    tail = tail[1:].strip()
    groups = []
    while True:
        top = list(top_positions(masked(tail)))
        if tail.startswith("∀"):
            comma = next(i for i,c in top if c == ",")
            clause = tail[1:comma].strip()
            colon = next((i for i,c in top_positions(clause) if c == ":"),None)
            if clause.startswith(tuple(PAIRS)):
                parsed = binders(clause,0)
                groups.extend(parsed)
            elif colon is not None:
                domain = clause[colon+1:].strip()
                category, reason = classification(domain)
                groups.append(dict(source=clause,domain_source=domain,category=category,reason=reason))
            else:
                groups.append(dict(source=clause,domain_source=None,category="unresolved",reason="untyped universal variables require elaboration"))
            tail = tail[comma+1:].strip()
            continue
        arrow = next((i for i,c in top if c == "→"),None)
        if arrow is None:
            return groups,tail
        clause = tail[:arrow].strip()
        parsed = binders(clause,0) if clause.startswith(tuple(PAIRS)) else []
        if len(parsed) == 1 and parsed[0]["source"] == clause:
            groups.extend(parsed)
        else:
            category,reason = classification(clause)
            groups.append(dict(source=clause,domain_source=clause,category=category,reason=reason))
        tail = tail[arrow+1:].strip()


def inventory(source_inventory):
    statements = []
    for original in source_inventory["theorems"]:
        contexts = []
        for ctx in original["context_commands"]:
            if ctx["kind"] == "variable":
                m = re.match(r"variable\b", ctx["source"])
                contexts.extend(binders(ctx["source"],m.end()))
        derived,conclusion = result_inputs(original)
        aliases = {"values":6} if original["source_qualified_name"] == "Solidity.Lowering.V07.P12AssignedConditionControls.bool_reflect" else {}
        classified = classify_binders(contexts+original["binder_evidence"]+derived,aliases)
        statements.append(dict(name=original["source_qualified_name"],path=original["path"],line=original["line"],
            signature_sha256=original["signature_sha256"],owner=original["owner"],
            explicit_binders=classified[len(contexts):len(contexts)+len(original["binder_evidence"])],context_binder_candidates=classified[:len(contexts)],
            result_type_inputs=classified[len(contexts)+len(original["binder_evidence"]):],source_conclusion=conclusion,
            context_membership="pending elaborated telescope; candidates are not asserted to occur in the theorem",
            result_telescope_status="source outer forall/arrows extracted; inferred types and elaborated fidelity pending",
            simultaneous_witness="pending",fidelity="pending elaboration"))
    counts = collections.Counter(b["kind"] for r in statements for b in r["explicit_binders"])
    unresolved = [dict(name=r["name"],path=r["path"],owner=r["owner"],binder=b) for r in statements for b in r["explicit_binders"] if b["kind"] in ("unresolved","abstract-predicate-application")]
    assert len(statements) == source_inventory["theorem_count"] == 968
    assert len({r["name"] for r in statements}) == 968
    return dict(schema=1,boundary="Source-evidenced premise roles, not elaboration, a complete semantic telescope, or a witness.",
        source_map_sha256=source_inventory["map_sha256"],statements=statements,explicit_kind_counts=dict(counts),
        explicit_resolution_queue=unresolved,explicit_resolution_queue_count=len(unresolved),
        result_resolution_queue=[dict(name=r["name"],path=r["path"],owner=r["owner"],binder=b) for r in statements for b in r["result_type_inputs"] if b["kind"] == "unresolved"],
        context_resolution_queue=[dict(name=r["name"],path=r["path"],owner=r["owner"],binder=b) for r in statements for b in r["context_binder_candidates"] if b["kind"] == "unresolved"],
        statement_count=len(statements),explicit_binder_count=sum(counts.values()),
        result_input_group_count=sum(len(r["result_type_inputs"]) for r in statements),
        result_input_kind_counts=dict(collections.Counter(b["kind"] for r in statements for b in r["result_type_inputs"])))


if __name__ == "__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo",type=pathlib.Path,required=True)
    p.add_argument("--inventory",type=pathlib.Path,required=True)
    p.add_argument("--output",type=pathlib.Path,required=True)
    a=p.parse_args()
    original=json.loads(a.inventory.read_text())
    result=inventory(original)
    result["predicate_source_facts"]=predicate_facts(a.repo,original["modules"])
    family = next(row for row in original["structures"] if row["source_qualified_name"] == "Solidity.Lowering.V07.IntegerLocalFamily")
    assert re.search(r":\s*Prop\s*$",masked(family["signature_source"]))
    result["prop_structure_fact"] = dict(name=family["source_qualified_name"],path=family["path"],start=family["start"],end=family["end"],header_source=family["signature_source"],header_sha256=family["signature_sha256"],module_sha256=family["module_sha256"])
    values_path = a.repo/"Solidity/Lowering/V07/P12AssignedConditionControls.lean"
    values_source = values_path.read_text()
    m = re.search(r"^def values : ValueRelation E C :=",values_source,re.M)
    assert m is not None
    result["local_alias_fact"] = dict(name="Solidity.Lowering.V07.P12AssignedConditionControls.values",path=str(values_path.relative_to(a.repo)),source=m[0],start=m.start(),end=m.end(),module_sha256=hashlib.sha256(values_path.read_bytes()).hexdigest(),basis="ValueRelation E C has six source parameters and Prop codomain in P12NextInterface; exact constant resolution pending")
    result["source_inventory_sha256"]=hashlib.sha256(a.inventory.read_bytes()).hexdigest()
    a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({k:result[k] for k in ("statement_count","explicit_binder_count","explicit_kind_counts","explicit_resolution_queue_count")}))
