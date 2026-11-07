#!/usr/bin/env python3
"""Exact source slices and provisional premise evidence, never elaborated types.

Supported source grammar is checked against every mapped declaration. Unresolved
semantic categories remain explicit; no witness or inhabitation is inferred.
"""
import argparse
import hashlib
import json
import pathlib
import re
from census import census, masked

PAIRS = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
CLOSE = set(PAIRS.values())


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def terminator(code, start, structure=False):
    stack = []
    i = start
    while i < len(code):
        c = code[i]
        if not stack:
            if code.startswith(":=", i):
                return i, ":="
            if structure and re.match(r"where\b", code[i:]):
                return i, "where"
            if c == "|":
                return i, "equations"
        if c in PAIRS:
            stack.append(PAIRS[c])
        elif c in CLOSE:
            if not stack or stack.pop() != c:
                raise ValueError(f"unbalanced signature at {i}")
        i += 1
    raise ValueError(f"no signature terminator at {start}")


def context(source, code, offset):
    frames = [("root", "", [])]
    for m in re.finditer(r"^(namespace|section|end|variable|include|omit|open|universe)\b([^\n]*)", code[:offset], re.M):
        kind, rest = m[1], m[2].strip()
        if kind in ("namespace", "section"):
            frames.append((kind, rest, []))
        elif kind == "end":
            if len(frames) == 1:
                raise ValueError("unmatched end")
            frames.pop()
        else:
            finish = code.find("\n", m.end())
            finish = len(code) if finish < 0 else finish
            # variable/open commands can continue on indented lines.
            while finish < len(code):
                nxt = code.find("\n", finish+1)
                nxt = len(code) if nxt < 0 else nxt
                line = code[finish+1:nxt]
                if line.strip() and not line[0].isspace():
                    break
                if not line.strip():
                    break
                finish = nxt
            frames[-1][2].append({"kind": kind, "source": source[m.start():finish],
                                  "start": m.start(), "end": finish})
    namespace = ".".join(name for kind, name, _ in frames if kind == "namespace")
    return namespace, [item for _, _, items in frames for item in items]


def classification(domain):
    # Source-level evidence only. A named structure does not imply inhabitation.
    if domain == "P8a.Spec":
        return "global-source-specification", "P8.FrozenInterface Spec aliases Roadmap.SourceSpec; its fields are global semantic obligations, not an input witness."
    if domain == "P8a.OperationalReference":
        return "global-operational-reference", "Frozen reference supplies Resource/points/Executes; actual-source adequacy remains a separate obligation."
    if domain.startswith("P8a.SourceOrigins "):
        return "global-source-origin-model", "Frozen SourceOrigins supplies meaning for all well-formed in-profile resolutions; not a per-input admission witness."
    if domain.startswith("P8a.RootModel "):
        return "global-root-feature-model", "Frozen RootModel supplies execution/observation/feature relations and classification; no inhabitance or exact extraction follows."
    if "P8a.Producer" in domain:
        return "global-producer-contract", "Frozen producer bundles universally quantified laws; not a per-input run witness."
    if re.search(r"\b(?:Condition|MemoryCapture|StorageCapture)\b", domain):
        return "request-contract-candidate", "P12 contract has request-indexed success/revert fields; inhabitation and successful execution are separate obligations."
    if re.search(r"\b(?:DeclarationGraph|LocationDeclarationGraph|IntegerLocalFamily|ContextMap)\b", domain):
        return "indexed-certificate-or-map", "Indexed by an environment/context/location; not evidence of all-input compiler success."
    if re.search(r"\b(?:FieldsOK|UniqueNames|SelectionOK)\b", domain):
        return "environment-support-predicate", "Named Prop definitions in PrimitiveGraph/RecursiveGraph/LocationGraphProducer; support for this environment is not global compiler totality."
    if re.search(r"\b(?:ValueRelation|WorldRelation)\b", domain):
        return "relation-parameter", "P12 aliases end in Prop; choosing a relation does not establish initial alignment or execution."
    if re.search(r"\b(?:BindingRel|IntValueRel|AddressRel|FitsInt|NoFail|Rel)\b|∈", domain):
        return "per-input-predicate-candidate", "Source relation/range/failure predicate or membership; a simultaneous input witness is still required."
    if re.match(r"(?:R|values)\s", domain):
        return "abstract-relation-application", "Caller-supplied relation application; retain context commands to check its declared codomain."
    if domain.startswith("AcceptedGraph ") or domain == "producer.checkedFrontend.Cert":
        return "producer-dependent-certificate", "Depends on the frozen producer; certificate availability does not inhabit the producer."
    if domain == "Type":
        return "type-parameter", "Universe-level parameter; no inhabitant of the parameter type is implied."
    if domain == "ι":
        return "abstract-type-data", "Value of the caller's abstract type; type parameter alone does not imply Nonempty."
    if re.search(r"(?:=|≠|≤|≥|<|>|∧|∨|↔|¬|∀|∃|→|\b(?:Related|GraphTypeRel|GraphFieldsRel|Injective|Nodup|Nonempty|Supported|Aligned)\b)", domain):
        return "predicate-or-function-candidate", "Syntactic predicate/function markers; propositionhood and dependency scope require elaboration/review."
    if re.search(r"\b(?:Nat|Int|Bool|State|EMState|STy|IntTy|Ctx|RCtx|Layout|Env|Contract|Val|Idx|LTy|RExpr|Glob|Fr|DataLoc|DeclName|Fin|String|Name|Ty|Schema|HTy|Pipeline|Denote|TDenote|Address|Thin|TEnv|UInt8|BinOp|PrimTy|Input|Resolved|Q|Artifact|RefTy|Locals|Bytes|Settings|HRef|SRef|SPath|Out|St|THalt|Halt|Res|MapKey|Syn|Operand|Prefix|Stmt|RVal)\b", domain):
        return "data-or-index-candidate", "Named data/index type in source; dependent feasibility still requires a simultaneous witness."
    return "unresolved", "Source alone has no classification rule; retained for semantic review."


def binders(signature, name_end):
    code = masked(signature)
    result = []
    i = name_end
    while i < len(code):
        if code[i].isspace():
            i += 1
            continue
        if code[i] not in PAIRS:
            break
        start = i
        stack = [PAIRS[code[i]]]
        i += 1
        colon = None
        while stack:
            if i >= len(code):
                raise ValueError("unterminated binder")
            if len(stack) == 1 and code[i] == ":" and not code.startswith(":=", i) and colon is None:
                colon = i
            if code[i] in PAIRS:
                stack.append(PAIRS[code[i]])
            elif code[i] in CLOSE:
                if stack.pop() != code[i]:
                    raise ValueError("mismatched binder")
            i += 1
        domain = signature[colon+1:i-1].strip() if colon is not None else None
        category, reason = classification(domain) if domain is not None else ("unresolved", "No explicit binder type.")
        result.append({"source": signature[start:i], "domain_source": domain,
                       "category": category, "reason": reason,
                       "inhabitation": "unproved", "semantic_classification": "pending"})
    return result


def type_evidence(text):
    code = masked(text)
    stack = []
    arrows = []
    start = 0
    for i, c in enumerate(code):
        if c in PAIRS:
            stack.append(PAIRS[c])
        elif c in CLOSE:
            if not stack or stack.pop() != c:
                raise ValueError("unbalanced type")
        elif c == "→" and not stack:
            domain = text[start:i]
            category, reason = classification(domain)
            arrows.append({"source": domain, "category": category, "reason": reason})
            start = i+1
    return {"source": text, "top_level_arrow_domains": arrows,
            "quantifier_tokens": len(re.findall("[∀∃]", code)),
            "execution_markers": sorted(set(re.findall(r"(?:\.run|evalE|isSome|produce|frontend)", code))),
            "resource_markers": sorted(set(re.findall(r"\b(?:fuel|gas|fork|resource|Res|FailurePoints)\b", code))),
            "classification": "syntactic evidence only; quantifier scope and propositionhood pending review"}


def inventory(repo):
    old = census(repo)
    theorem_rows = []
    structures = []
    supplemental_path = "Solidity/Lowering/V07/DeclarationGraph.lean"
    supplemental = [{"path": supplemental_path, "sha256": hashlib.sha256((repo/supplemental_path).read_bytes()).hexdigest()}]
    supplemental_structures = []
    supplemental_theorems = []
    for module in old["modules"] + supplemental:
        path = module["path"]
        source = (repo/path).read_text()
        code = masked(source)
        matches = list(re.finditer(r"\b(theorem|lemma|structure)\s+([^\s({\[:]+)", code))
        for m in matches:
            start = m.start()
            end, term = terminator(code, m.end(), m[1] == "structure")
            signature = source[start:end]
            namespace, ctx = context(source, code, start)
            fq = m[2][7:] if m[2].startswith("_root_.") else ".".join(x for x in (namespace, m[2]) if x)
            row = {"source_qualified_name": fq, "local_name": m[2], "kind": m[1], "path": path,
                   "line": source.count("\n", 0, start)+1, "start": start, "end": end,
                   "signature_source": signature, "signature_sha256": digest(signature),
                   "terminator": term, "context_commands": ctx,
                   "source_prefix_sha256": digest(source[:start]), "module_sha256": module["sha256"],
                   "binder_evidence": binders(signature, m.end()-start),
                   "signature_type_evidence": type_evidence(signature[m.end()-start:]),
                   "context_variable_evidence": [dict(command=item, evidence=type_evidence(item["source"])) for item in ctx if item["kind"] == "variable"],
                   "owner": "V07 (v07-v11/v07-lowering)",
                   "statement_fidelity": "pending-elaboration", "simultaneous_witness": "pending",
                   "premise_completeness": "pending: result-type binders/arrows, implicit parameters, and imported predicates require semantic review"}
            if m[1] != "structure":
                if path == supplemental_path:
                    supplemental_theorems.append(row)
                else:
                    theorem_rows.append(row)
                continue
            body_start = end+len(term)
            next_command = re.search(r"^\S", code[body_start:], re.M)
            body_end = body_start+next_command.start() if next_command else len(code)
            fields = list(re.finditer(r"^  ([A-Za-z_][A-Za-z0-9_']*)\s*:", code[body_start:body_end], re.M))
            # Exclude trailing documentation belonging to the next command.
            substantive = list(re.finditer(r"\S", code[body_start:body_end]))
            body_end = body_start+substantive[-1].end()
            fields = list(re.finditer(r"^  ([A-Za-z_][A-Za-z0-9_']*)\s*:", code[body_start:body_end], re.M))
            row["contract_end"] = body_end
            row["contract_source"] = source[start:body_end]
            row["contract_sha256"] = digest(source[start:body_end])
            row["fields"] = []
            for i, field in enumerate(fields):
                fs = body_start+field.start()
                fe = body_start+fields[i+1].start() if i+1 < len(fields) else body_end
                substantive = list(re.finditer(r"\S", code[fs:fe]))
                fe = fs+substantive[-1].end()
                # Keep exact original source through the final substantive token.
                domain = source[body_start+field.end():fe]
                category, reason = classification(masked(domain))
                row["fields"].append({"source_qualified_name": fq+"."+field[1],
                    "start": fs, "end": fe, "source": source[fs:fe], "sha256": digest(source[fs:fe]),
                    "category": category, "reason": reason, "type_evidence": type_evidence(domain), "simultaneous_record_witness": "pending"})
            if not row["fields"]:
                raise ValueError(f"unparsed structure fields: {fq}")
            if path == supplemental_path:
                row["scope"] = "supplemental imported premise contract; not a mapped-module row"
                supplemental_structures.append(row)
            else:
                structures.append(row)
    assert len(theorem_rows) == old["candidate_count"]
    keys = [(r["path"], r["start"]) for r in theorem_rows]
    assert len(keys) == len(set(keys))
    return {"schema": 2, "boundary": "Exact original source slices; source-qualified names and binder categories are provisional, not elaborated signatures or proofs.",
            "scope": old["scope"], "map_sha256": old["map_sha256"], "modules": old["modules"],
            "module_count": old["module_count"], "theorem_count": len(theorem_rows),
            "structure_count": len(structures), "field_count": sum(len(r["fields"]) for r in structures),
            "theorems": theorem_rows, "structures": structures,
            "supplemental_modules": supplemental, "supplemental_structures": supplemental_structures, "supplemental_theorems": supplemental_theorems}


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", required=True, type=pathlib.Path)
    p.add_argument("--output", required=True, type=pathlib.Path)
    a = p.parse_args()
    result = inventory(a.repo)
    a.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps({k: result[k] for k in ("module_count", "theorem_count", "structure_count", "field_count")}))
