#!/usr/bin/env python3
"""Exhaustive SOURCE classification; never an elaborated feasibility proof.

Each census row stays in scope. Input binder domains, leading arrows/forall,
section context and Type-valued certificate fields remain visible. Unknown
sorts and missing producer owners are explicit blockers, never guessed away.
All source and definition evidence comes from the frozen Git tree.
"""
import argparse
import collections
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile
from census import BASE, mask, generate

OPEN = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩", "⟦": "⟧"}
CLOSE = set(OPEN.values())
IDENT = r"(?:[\w'?!]+|«[^»]+»)(?:\.(?:[\w'?!]+|«[^»]+»))*"
DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(namespace|section|mutual|end|variable|include|omit|open|theorem|lemma|structure|inductive|class|def|abbrev|opaque|axiom)\b([^\n]*)")
DATA_HEADS = {"Nat", "Int", "Bool", "String", "Char", "UInt8", "UInt16", "UInt32", "UInt64", "USize", "ByteArray", "List", "Array", "Option", "Except", "Prod", "Sum", "PSum", "PProd", "PUnit", "Unit", "Empty", "PEmpty", "Fin", "BitVec", "Subtype", "Sigma", "PSigma", "Finset", "Set", "Function", "Lean.Name", "Name", "StateM", "StateT", "ExceptT", "ReaderT", "EStateM", "Id"}
PROOF_HEADS = {"True", "False", "Eq", "HEq", "Ne", "And", "Or", "Not", "Iff", "Exists", "Nonempty", "List.Nodup", "List.Pairwise", "List.Mem", "List.Sublist", "List.IsPrefix", "List.Prefix", "List.Suffix", "List.Subset"}
REVIEWED_SCOPES = {
    "Solidity.Roadmap.PublicCorrectness": "global-law-bearing-structure",
    "Solidity.CtxEquiv.Validator": "global-conditional-validator-contract",
    "Solidity.Evm.External.Memory.PaddingCorrect": "global-bounded-allocator-law",
    "Solidity.Evm.External.Assembly.MacroRefinement": "universal-associated-code-execution-contract",
    "Solidity.Evm.External.Assembly.Boundary": "per-input-state-relation",
    "Solidity.Evm.External.Memory.Represents": "per-input-state-relation",
    "Solidity.Source.Agreement.NormalStmtObligation": "universal-associated-statement-contract",
    "Solidity.Source.Agreement.NormalLocalsObligation": "universal-associated-program-contract",
}
DECL_KINDS = {"theorem", "lemma", "structure", "inductive", "class", "def", "abbrev", "opaque", "axiom"}

def sha(text): return hashlib.sha256(text.encode()).hexdigest()

def top_tokens(text):
    """Yield character offsets at delimiter depth zero; no precedence claims."""
    stack = []
    for i, char in enumerate(text):
        if not stack: yield i
        if char in OPEN: stack.append(OPEN[char])
        elif char in CLOSE:
            if not stack or stack.pop() != char: raise ValueError("unbalanced delimiter")
    if stack: raise ValueError("unclosed delimiter")

def at_top(text, needle):
    return [i for i in top_tokens(text) if text.startswith(needle, i)]

def group_end(text, start):
    stack = [OPEN[text[start]]]
    for i in range(start + 1, len(text)):
        char = text[i]
        if char in OPEN: stack.append(OPEN[char])
        elif char in CLOSE:
            if stack.pop() != char: raise ValueError("mismatched group")
            if not stack: return i + 1
    raise ValueError("unterminated group")

def strip_outer(text):
    text = text.strip()
    while text.startswith("(") and group_end(text, 0) == len(text): text = text[1:-1].strip()
    return text

def binder_group(group, origin):
    opening = group[0]
    inside = group[1:-1].strip()
    colons = [i for i in at_top(inside, ":") if not inside.startswith(":=", i)]
    if colons:
        names_text, domain = inside[:colons[0]], inside[colons[0]+1:].strip()
        defaults = at_top(domain, ":=")
        if defaults: domain = domain[:defaults[0]].strip()
        names = re.findall(IDENT, names_text)
    elif opening == "[":
        names, domain = ["_instance"], inside
    else:
        names, domain = re.findall(IDENT, inside), None
    if not names: names = ["_anonymous"]
    return [{"name": name, "domain": domain, "origin": origin,
             "binder_kind": {"(": "explicit", "{": "implicit", "⦃": "strict-implicit", "[": "instance"}[opening],
             "source_group": group} for name in names]

def leading_groups(text, origin):
    groups = []
    cursor = 0
    while cursor < len(text):
        if text[cursor].isspace(): cursor += 1; continue
        if text[cursor] not in "({[⦃": break
        end = group_end(text, cursor)
        groups.extend(binder_group(text[cursor:end], origin))
        cursor = end
    return groups, text[cursor:].strip()

def signature_parts(signature):
    clean = mask(signature)
    found = re.search(r"\b(?:theorem|lemma)\s+" + IDENT, clean)
    if not found: raise ValueError("missing named theorem command")
    binders, rest = leading_groups(clean[found.end():], "header")
    if not rest.startswith(":"): raise ValueError("missing theorem result colon")
    return binders, rest[1:].strip()

def result_spine(result):
    """Read only the leading Pi spine. Stop at existential/iff conclusions."""
    binders = []
    rest = strip_outer(result)
    while rest:
        if rest.startswith("∀"):
            tail = rest[1:].strip()
            commas = at_top(tail, ",")
            if not commas: raise ValueError("forall without top-level comma")
            declaration, rest = tail[:commas[0]], tail[commas[0]+1:].strip()
            groups, extra = leading_groups(declaration, "leading-forall")
            binders.extend(groups)
            if extra:
                # Bare quantified binders can infer their types; retain the
                # entire clause rather than inventing a type or membership proof.
                binders.append({"name": "_inferred_forall", "domain": None,
                                "origin": "leading-forall", "binder_kind": "inferred",
                                "source_group": extra})
            rest = strip_outer(rest)
            continue
        if rest.startswith(("∃", "fun ", "let ")): break
        arrows = at_top(rest, "→") + at_top(rest, "->")
        # Iff binds more weakly than arrows; an implication inside its RHS
        # belongs to the conclusion, not to this theorem's leading telescope.
        if not arrows or at_top(rest, "↔") or at_top(rest, "<->"): break
        arrow = min(arrows)
        left, right = rest[:arrow].strip(), rest[arrow + (2 if rest.startswith("->", arrow) else 1):].strip()
        grouped = False
        if left.startswith(tuple("({[⦃")) and group_end(left, 0) == len(left):
            interior = left[1:-1]
            if any(not interior.startswith(":=", i) for i in at_top(interior, ":")) or left[0] in "{[⦃":
                binders.extend(binder_group(left, "leading-arrow")); grouped = True
        if not grouped:
            binders.append({"name": "_arrow_" + str(len(binders)), "domain": left,
                            "origin": "leading-arrow", "binder_kind": "anonymous",
                            "source_group": left})
        rest = strip_outer(right)
    return binders, rest

def frozen_sources():
    payload = subprocess.check_output(["git", "archive", BASE, "Solidity", "Bridge"])
    with tarfile.open(fileobj=io.BytesIO(payload)) as archive:
        return {member.name: archive.extractfile(member).read().decode()
                for member in archive if member.isfile() and member.name.endswith(".lean")}

def declaration_index(sources):
    """Index source-declared sorts/fields; ambiguous names remain ambiguous."""
    symbols = {}
    by_tail = collections.defaultdict(list)
    for path, source in sources.items():
        clean = mask(source)
        events = list(DECL.finditer(clean))
        stack = []
        for n, event in enumerate(events):
            kind, tail = event[1], event[2].strip()
            if kind in ("namespace", "section", "mutual"):
                stack.append((kind, tail.split()[0] if tail else "")); continue
            if kind == "end":
                if stack: stack.pop()
                continue
            if kind not in DECL_KINDS: continue
            name = re.match(IDENT, tail)
            if not name: continue
            prefix = ".".join(x[1] for x in stack if x[0] == "namespace")
            qualified = name[0][7:] if name[0].startswith("_root_.") else ".".join(x for x in (prefix, name[0]) if x)
            stop = events[n+1].start() if n+1 < len(events) else len(clean)
            block = clean[event.end(1):stop]
            starts = re.match(r"\s*" + IDENT, block)
            if not starts: continue
            tailblock = block[starts.end():]
            header = ""
            body = ""
            parameters = []
            try:
                offsets = at_top(tailblock, ":=") + [m.start() for m in re.finditer(r"\bwhere\b", tailblock) if m.start() in set(top_tokens(tailblock))]
                stop_header = min(offsets) if offsets else len(tailblock)
                header = tailblock[:stop_header]
                body = tailblock[stop_header+2:].strip() if tailblock[stop_header:].startswith(":=") else tailblock[stop_header:].strip()
                parameters, result = leading_groups(header, "definition")
                result = result[1:].strip() if result.startswith(":") else ""
            except ValueError:
                result = ""
            try:
                _, result_tail = result_spine(result) if result else ([], "")
            except ValueError:
                result_tail = result
            result_tail = result_tail.strip()
            prop = bool(re.match(r"^Prop(?:\s+extends\b|\s*$)", result_tail))
            if kind in ("theorem", "lemma"): category = "proof-constant"
            elif prop: category = "predicate-symbol"
            elif kind in ("structure", "inductive", "class"): category = "type-symbol"
            elif re.match(r"^(?:Type|Sort)(?:\s|$|\()", result_tail): category = "type-symbol"
            else: category = "source-sort-unresolved"
            fields = []
            if kind in ("structure", "class"):
                starts_fields=list(re.finditer(r"(?m)^  ([\w'?!]+)\b",block))
                for fi, field in enumerate(starts_fields):
                    field_end=starts_fields[fi+1].start() if fi+1<len(starts_fields) else len(block)
                    field_text=block[field.end():field_end].strip()
                    try:
                        field_parameters, field_tail=leading_groups(field_text,"structure-field")
                        if not field_tail.startswith(":"): continue
                        domain=field_tail[1:].strip()
                        # Stop at any later top-level command not recognized
                        # by DECL; it is not part of this structure field.
                        lines=domain.splitlines()
                        for li,line in enumerate(lines[1:],1):
                            if line.strip() and not line.startswith("  "):
                                domain="\n".join(lines[:li]);break
                        defaults=at_top(domain,":=")
                        default=domain[defaults[0]+2:].strip() if defaults else None
                        if defaults: domain=domain[:defaults[0]].strip()
                        if field_parameters:
                            domain=" → ".join(b["source_group"] for b in field_parameters)+" → "+domain
                    except ValueError: continue
                    fields.append({"name":field[1],"domain":domain,
                                   "default_source":default,"has_explicit_forall":"∀" in domain})
            record = {"name": qualified, "path": path,
                      "line": source.count("\n", 0, event.start(1))+1,
                      "kind": kind, "declared_result": result, "parameters": parameters,
                      "category": category, "fields": fields,
                      "body_has_forall": "∀" in body, "rhs_prefix": body[:400],
                      "source_block_sha256": sha(source[event.start():stop])}
            # The same full name can occur in separate package roots/private
            # namespaces. Keep all candidates rather than silently overwrite.
            key = path + ":" + str(record["line"]) + ":" + qualified
            record["id"] = key
            symbols[key] = record
            by_tail[qualified.split(".")[-1]].append(key)
    # Inferred aliases such as Ctx := List LTy and EM := ExceptT ... are
    # source type expressions. Resolve only known Type constructors/aliases;
    # arbitrary inferred definitions remain unresolved.
    changed = True
    while changed:
        changed = False
        for record in symbols.values():
            if record["category"] != "source-sort-unresolved" or record["declared_result"]: continue
            rhs = record["rhs_prefix"]
            if not rhs or rhs.startswith(("if ", "match ", "let ", "fun ")): continue
            try:
                _, terminal = result_spine(rhs)
                terminal = strip_outer(terminal)
            except ValueError: continue
            head = re.match(IDENT, terminal)
            if not head: continue
            hits = resolve(head[0],record["name"].rsplit(".",1)[0],symbols,by_tail)
            if terminal == "Prop" and ("→" in rhs or "->" in rhs):
                record["category"]="type-symbol"
                record["alias_parameter_role"]="predicate-parameter"
                changed=True
                continue
            if head[0] in DATA_HEADS or (hits and len({x["name"] for x in hits})==1 and all(x["category"]=="type-symbol" for x in hits)):
                record["category"]="type-symbol"
                record["alias_basis"]="inferred alias body ends in known source Type constructor"
                changed=True
    return symbols, by_tail

def resolve(head, namespace, symbols, by_tail):
    pieces = namespace.split(".")
    for n in range(len(pieces), -1, -1):
        target = ".".join(pieces[:n] + [head])
        hits = [symbols[k] for k in by_tail.get(head.split(".")[-1], []) if symbols[k]["name"] == target]
        if hits: return hits
    return [symbols[k] for k in by_tail.get(head.split(".")[-1], []) if symbols[k]["name"].endswith("."+head) or symbols[k]["name"] == head]

def source_sort(domain, namespace, local, symbols, by_tail, used):
    if domain is None: return "unresolved-inferred-type", []
    domain = strip_outer(domain)
    if domain == "Prop": return "proposition-parameter", []
    if re.match(r"^(?:Type|Sort)(?:\s|$|\()", domain): return "type-parameter", []
    if domain.startswith(("if ", "match ", "let ")): return "source-sort-unresolved", []
    if domain.startswith("Σ"): return "dependent-data-parameter", []
    if domain.startswith("∀"):
        try:
            _, terminal = result_spine(domain)
            role, refs = source_sort(terminal, namespace, local, symbols, by_tail, used)
            return ("proof-premise" if role == "proof-premise" else "function-or-quantified-domain-unresolved"), refs
        except ValueError: return "function-or-quantified-domain-unresolved", []
    if domain.startswith("∃"): return "proof-premise", []
    arrows = at_top(domain, "→") + at_top(domain, "->")
    if arrows and not at_top(domain, "↔") and not at_top(domain, "<->"):
        arrow = max(arrows)
        terminal = domain[arrow+(2 if domain.startswith("->",arrow) else 1):]
        role, refs = source_sort(terminal, namespace, local, symbols, by_tail, used)
        if role == "proposition-parameter": return "predicate-parameter", refs
        if role == "proof-premise": return "proof-premise", refs
        if role in ("type-parameter", "data-parameter", "certificate-carrying-data", "structure-parameter", "data-at-abstract-type", "dependent-data-parameter"): return "function-parameter", refs
        return "function-or-quantified-domain-unresolved", refs
    operators = ("=", "≠", "≤", "≥", "<", ">", "∈", "∉", "⊆", "⊢", "⊨", "⊧", "∧", "∨", "↔", "≃")
    if domain.startswith("¬") or any(at_top(domain, op) for op in operators): return "proof-premise", []
    matched = re.match(IDENT, domain)
    if not matched: return "source-sort-unresolved", []
    head = matched[0]
    if head in local:
        role = local[head]["sort"]
        if role in ("proposition-parameter", "predicate-parameter"): return "proof-premise", []
        if role == "type-parameter": return "data-at-abstract-type", []
    if head in PROOF_HEADS: return "proof-premise", []
    if head in DATA_HEADS: return "data-parameter", []
    # Projection notation through a locally typed source structure can name
    # either a data field (S.Input) or a predicate field (S.Admitted).
    if "." in head:
        receiver, field = head.split(".",1)
        if receiver in local:
            for key in local[receiver]["definition_evidence"]:
                structure = symbols[key]
                matches = [f for f in structure["fields"] if f["name"]==field]
                if matches:
                    field_domain = matches[0]["domain"]
                    try: _, terminal = result_spine(field_domain)
                    except ValueError: terminal=""
                    used[key]=structure
                    if terminal.strip()=="Prop": return "proof-premise", [key]
                    if re.match(r"^(?:Type|Sort)(?:\s|$|\()",terminal.strip()): return "data-parameter",[key]
                methods=resolve(structure["name"]+"."+field,namespace,symbols,by_tail)
                if methods and len({m["name"] for m in methods})==1:
                    for method in methods: used[method["id"]]=method
                    if all(m["category"]=="predicate-symbol" for m in methods): return "proof-premise",[m["id"] for m in methods]
                    if all(m["category"]=="type-symbol" for m in methods): return "data-parameter",[m["id"] for m in methods]
    candidates = resolve(head, namespace, symbols, by_tail)
    refs = [r["id"] for r in candidates]
    for record in candidates: used[record["id"]] = record
    if len({r["name"] for r in candidates})>1:
        return "ambiguous-source-symbol-unresolved",refs
    kinds = {r["category"] for r in candidates}
    if kinds == {"predicate-symbol"}: return "proof-premise", refs
    if kinds == {"type-symbol"}:
        if candidates and all(r.get("alias_parameter_role")=="predicate-parameter" for r in candidates): return "predicate-parameter",refs
        proof_fields = []
        for record in candidates:
            for field in record["fields"]:
                try: _, terminal = result_spine(field["domain"])
                except ValueError: continue
                term_head=re.match(IDENT,terminal)
                term_hits=resolve(term_head[0],record["name"].rsplit(".",1)[0],symbols,by_tail) if term_head else []
                projected_predicate=False
                if term_head and "." in term_head[0]:
                    receiver, member=term_head[0].split(".",1)
                    for parameter in record["parameters"]:
                        if parameter["name"]!=receiver or not parameter["domain"]: continue
                        owner_head=re.match(IDENT,parameter["domain"])
                        owners=resolve(owner_head[0],record["name"].rsplit(".",1)[0],symbols,by_tail) if owner_head else []
                        if len({owner["name"] for owner in owners})!=1: continue
                        for owner in owners:
                            for projected in owner["fields"]:
                                if projected["name"]!=member: continue
                                try: _,last=result_spine(projected["domain"])
                                except ValueError: continue
                                if last=="Prop": projected_predicate=True
                            methods=resolve(owner["name"]+"."+member,namespace,symbols,by_tail)
                            if methods and all(method["category"]=="predicate-symbol" for method in methods): projected_predicate=True
                if terminal.startswith(("¬","∃")) or terminal in PROOF_HEADS or any(at_top(terminal,op) for op in ("=","≠","≤","≥","<",">","∈","∧","↔")) or (term_hits and all(r["category"]=="predicate-symbol" for r in term_hits)) or projected_predicate:
                    proof_fields.append(field)
        if proof_fields: return "certificate-carrying-data", refs
        if any(r["fields"] for r in candidates): return "structure-parameter", refs
        return "data-parameter", refs
    return "source-sort-unresolved", refs

def owner_roles(claims):
    roles = collections.defaultdict(list)
    for claim in claims:
        if claim["id"].startswith("H62-6-") or "migration" in claim["mode"]: role = "migration"
        elif claim["id"].startswith("H62-1-"): role = "cleanup-writer"
        elif claim["id"].startswith("H62-2-"): role = "audit"
        else: role = "documented-live-reservation"
        roles[role].append(claim)
    producers = sorted({c["owner"] for c in roles["documented-live-reservation"] if c["owner"]})
    return {"classification": "documented-live-owner" if len(producers)==1 else "distinct-owner-conflict" if len(producers)>1 else "cleanup-writer-only-producer-unresolved" if roles["cleanup-writer"] else "no-documented-live-producer",
            "live_producer_owners": producers, "claims_by_role": dict(roles),
            "coordinator_routing_required": len(producers) != 1,
            "producer_confirmation": "Documented scope owner is a routing owner; semantic producer identity is not invented",
            "write_authorization": "none; classification is read-only"}

def classify_row(row, symbols, by_tail, used):
    header, result = signature_parts(row["source_signature"])
    leading, conclusion = result_spine(result)
    local = {}
    context = []
    namespace = row["name_candidate"].rsplit(".",1)[0]
    def annotate(binder):
        if binder["domain"] is None and binder["name"] in local:
            binder = dict(binder, domain=local[binder["name"]]["domain"], rebinding=True)
        sort, refs = source_sort(binder["domain"], namespace, local, symbols, by_tail, used)
        output = dict(binder, sort=sort, definition_evidence=refs,
                      inhabitance="not-established-by-source-classification")
        if binder["binder_kind"] == "instance": output["role"] = "typeclass-requirement"
        else: output["role"] = sort
        if binder["domain"] is not None:
            output["dependencies"] = sorted(set(re.findall(IDENT,binder["domain"])) & set(local))
        else: output["dependencies"] = []
        universal = [k for k in refs if used[k]["body_has_forall"] or any(f["has_explicit_forall"] for f in used[k]["fields"])]
        output["universal_contract_definition_candidates"] = universal
        output["reviewed_premise_scopes"] = sorted({REVIEWED_SCOPES[used[k]["name"]] for k in refs if used[k]["name"] in REVIEWED_SCOPES})
        if output["reviewed_premise_scopes"]:
            output["scope_evidence_status"]="manually reviewed source definition; inhabitance not established"
        else:
            output["scope_evidence_status"]="not semantically inferred from name, dependency, or Type/Prop alone"
        local[binder["name"]] = output
        return output
    for command in row["section_variables"]:
        clean = mask(command)
        start = re.search(r"\bvariables?\b", clean)
        if start:
            groups, _ = leading_groups(clean[start.end():],"section-context")
            context.extend(annotate(b) for b in groups)
    binders = [annotate(b) for b in header+leading]
    signature_ids = set(re.findall(IDENT,mask(row["source_signature"])))
    needed = set(signature_ids)
    for binder in reversed(context):
        if binder["name"] in needed: needed.update(binder["dependencies"])
    for binder in context:
        binder["activation"] = "referenced-dependency-closure" if binder["name"] in needed else "context-only-inclusion-needs-Lean"
    relevant = [b for b in context if b["name"] in needed] + binders
    roles = collections.Counter(b["role"] for b in relevant)
    ambiguous = [b for b in relevant if "unresolved" in b["role"] or b["role"]=="unresolved-inferred-type"]
    record = {"source_id": row["id"], "target_name_candidate": row["name_candidate"],
              "path": row["path"], "line": row["line"],
              "signature_sha256": row["signature_sha256"], "source_prefix_sha256": row["source_prefix_sha256"],
              "visibility": "private" if re.search(r"\bprivate\s+(?:theorem|lemma)\b",mask(row["source_signature"])) else "public-or-protected",
              "in_scope": True, "exclusion": None,
              "classification_level": "source-evidence-only; imported semantic telescope pending",
              "section_context": context, "explicit_and_leading_binders": binders,
              "conclusion_source": conclusion, "role_counts": dict(sorted(roles.items())),
              "source_sort_resolution": "contains-unresolved-domains" if ambiguous else "all-header-and-referenced-context-domains-source-classified",
              "section_inclusion": "Lexical dependencies only; include/omit/open and auto-implicit inclusion require original prefix/Lean",
              "global_vs_per_input": "Universal definition candidates and tuple dependencies recorded separately; no blanket global/per-input inference",
              "tuple_obligation": "All actual elaborated parameters and hypotheses must be jointly instantiated, including Type-valued certificates and instance arguments",
              "witness_status": "not-established-by-classification"}
    return record

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--census",type=Path,required=True)
    p.add_argument("--output",type=Path,required=True)
    args = p.parse_args()
    if args.output.resolve().is_relative_to(Path(__file__).resolve().parents[4]):
        raise ValueError("bulk classification output must be outside the repository")
    census = json.loads(args.census.read_text())
    if census["base"] != BASE or census["scan_errors"] or census["unresolved_references"]: raise ValueError("invalid frozen census")
    # External bulk JSON is evidence input, not authority. Recompute both the
    # complete frozen census and pinned ownership claims before trusting rows.
    if census != generate(): raise ValueError("census differs from frozen source or pinned ownership snapshot")
    sources = frozen_sources()
    directive_history={}
    for path in census["sources"]:
        clean=mask(sources[path])
        directive_history[path]=[{"kind":m[1],"line":clean.count("\n",0,m.start(1))+1,
                                  "source":sources[path].splitlines()[clean.count("\n",0,m.start(1))].strip()}
                                 for m in DECL.finditer(clean) if m[1] in ("include","omit","open")]

    for path, meta in census["sources"].items():
        if sha(sources[path]) != meta["sha256"]: raise ValueError("frozen file mismatch: "+path)
    symbols, by_tail = declaration_index(sources)
    used = {}
    owners = {path: owner_roles(meta["ownership_claims"]) for path,meta in census["sources"].items()}
    rows, errors = [], []
    for row in census["declarations"]:
        try: classified = classify_row(row,symbols,by_tail,used)
        except (ValueError, RecursionError) as error:
            classified = {"source_id":row["id"],"path":row["path"],"line":row["line"],
                          "target_name_candidate":row["name_candidate"],"signature_sha256":row["signature_sha256"],
                          "in_scope":True,"exclusion":None,"classification_level":"source-parse-blocker",
                          "error":str(error),"witness_status":"uncovered"}
            errors.append({"source_id":row["id"],"error":str(error)})
        classified["source_directive_history"]=[d for d in directive_history[row["path"]] if d["line"]<row["line"]]
        classified["directive_history_boundary"]="Original prefix history only; not a claim that prior one-shot directives remain active"
        classified["owner"] = owners[row["path"]]
        rows.append(classified)
    ids = [r["source_id"] for r in rows]
    if len(ids)!=len(set(ids)) or set(ids)!={r["id"] for r in census["declarations"]}: raise ValueError("census mismatch")
    routing = [{"path":path,"declarations":[r["source_id"] for r in rows if r["path"]==path],"owner_classification":owners[path]} for path in sorted(owners) if owners[path]["coordinator_routing_required"]]
    summary = {"base":BASE,"source_candidates":len(rows),"files":len(owners),"excluded":0,
               "source_parse_errors":len(errors),"owner_files":dict(collections.Counter(v["classification"] for v in owners.values())),
               "owner_declarations":dict(collections.Counter(r["owner"]["classification"] for r in rows)),
               "source_sort_resolution":dict(collections.Counter(r.get("source_sort_resolution","parse-blocked") for r in rows)),
               "semantic_classification_complete":False,"new_witness_claims":0}
    result = {"summary":summary,
              "generator_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "census_generator_sha256":hashlib.sha256(Path(__file__).with_name("census.py").read_bytes()).hexdigest(),
              "census_canonical_sha256":sha(json.dumps(census,sort_keys=True,separators=(",",":"),ensure_ascii=False)),"definitions_used":used,"declarations":rows,"parse_errors":errors,
              "ownership_source":"checksum-verified original ownership snapshot; no new authority inferred",
              "classification_boundary":"Source syntax and source-declared sorts only. No inhabitance, statement repair, proof, exclusion, or imported semantic certification is implied."}
    args.output.mkdir(parents=True,exist_ok=True)
    payload=(json.dumps(result,indent=2,ensure_ascii=False,sort_keys=True)+"\n").encode()
    (args.output/"classification.json").write_bytes(payload)
    (args.output/"classification.sha256").write_text(hashlib.sha256(payload).hexdigest()+"  classification.json\n")
    pending=[{"source_id":r["source_id"],"path":r["path"],"line":r["line"],
              "signature_sha256":r["signature_sha256"],
              "unresolved_binders":[b for b in r.get("explicit_and_leading_binders",[])+r.get("section_context",[]) if "unresolved" in b["role"]],
              "owner":r["owner"]} for r in rows if r.get("source_sort_resolution")=="contains-unresolved-domains"]
    (args.output/"unresolved-domains.json").write_text(json.dumps(pending,indent=2,ensure_ascii=False)+"\n")
    (args.output/"owner-routing.json").write_text(json.dumps({"routing":"coordinator; no master owner invented", "requests":routing},indent=2,ensure_ascii=False)+"\n")
    print(json.dumps(summary,sort_keys=True))
    return int(bool(errors))

if __name__ == "__main__": raise SystemExit(main())
