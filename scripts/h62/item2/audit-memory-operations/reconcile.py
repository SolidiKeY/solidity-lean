#!/usr/bin/env python3
"""Reconcile source candidates to area routes and source-level premise bundles.

No kernel name/type, exact file ownership, satisfiability, or completion claim.
This enriches rather than filters the frozen conservative census. Output off git.
"""
import argparse
import collections
import fnmatch
import hashlib
import importlib.util
import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("source_census", HERE / "census.py")
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)
PAIRS = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def prefix_end(clean, kind):
    """Locate source header end, consuming top-level conclusion-local let :=.

    This remains lexical; the complete source region is always retained and
    exact implicit/section/type elaboration is explicitly pending.
    """
    stack, lets, top_match = [], 0, False
    for match in re.finditer(r"⦃|⦄|[()\[\]{}]|\blet\b|\bmatch\b|\bwhere\b|:=|^[ \t]*\|", clean, re.M):
        token = match[0].strip()
        if token in PAIRS:
            stack.append(PAIRS[token])
        elif token in PAIRS.values():
            if not stack or stack.pop() != token:
                raise ValueError("Unbalanced source delimiter")
        elif not stack:
            if token == "let": lets += 1
            elif token == "match": top_match = True
            elif token == "|" and kind in ("theorem", "lemma"):
                # A top-level match in the type is ambiguous without Lean parsing.
                if top_match: return None, None
                return match.start(), match.end()
            elif token == "where" and kind in ("structure", "class"):
                return match.start(), match.end()
            elif token == ":=":
                if lets: lets -= 1
                else: return match.start(), match.end()
    return len(clean), len(clean)

def outer_binders(prefix):
    clean = census.mask(prefix)
    decl = re.search(r"\b(?:theorem|lemma|structure|class|axiom)\s+[^\s:(\[{]+", clean)
    if not decl: raise ValueError("Declaration header absent")
    result, i = [], decl.end()
    while i < len(clean):
        while i < len(clean) and clean[i].isspace(): i += 1
        if i == len(clean) or clean[i] not in PAIRS: break
        start, stack = i, [PAIRS[clean[i]]]
        i += 1
        while i < len(clean) and stack:
            if clean[i] in PAIRS: stack.append(PAIRS[clean[i]])
            elif clean[i] in PAIRS.values():
                if stack.pop() != clean[i]: raise ValueError("Mismatched binder")
            i += 1
        if stack: raise ValueError("Unclosed binder")
        inner = clean[start+1:i-1]
        colon = None
        depth = 0
        for j, char in enumerate(inner):
            if char in PAIRS: depth += 1
            elif char in PAIRS.values(): depth -= 1
            elif char == ":" and depth == 0:
                colon = j; break
        result.append(dict(source=prefix[start:i], start=start, end=i,
            binder_style=clean[start],
            names=inner[:colon].split() if colon is not None else [],
            type_source=prefix[start+1:i-1][colon+1:].strip() if colon is not None else prefix[start+1:i-1].strip(),
            classification="source binder; Prop/Type and feasibility unresolved"))
    return result

CUES = {
    "representation": r"\b(?:AllocatorRepr|StateRepr|StructAllocatorRepr|Sim|ReprAt|WordFrame|HeapRepr|FrameRepr)\b",
    "capacity-stack-budget": r"\b(?:cursor|cost|capacity|stack|Fits|room|gas)\b",
    "execution-resolution": r"\b(?:run|execS|evalE|resolveT|mvalT|checkedRun|runSlice|enter|entry)\b",
    "selection-admission-typing": r"\b(?:compile|compileDefault|compileStmt|selected|admitted|pathTy|mapFree|spathIn)\b",
    "bounds-arithmetic": r"[≤<>]|\b(?:length|bound|fits)\b",
    "dependent-index": r"\b(?:Fin|Idx|HRef|Entries|SVec)\b",
    "equality-coherence": r"=|\b(?:HEq|Coherence|coherent)\b",
    "named-contract-record": r"\b\w*(?:Certificate|Producer|Premise|Witness|Builder|Agreement|Coverage)\b",
}

def cues(source):
    clean = census.mask(source)
    return sorted(name for name, pattern in CUES.items() if re.search(pattern, clean))

def field_regions(region, body_start):
    clean = census.mask(region)
    matches = list(re.finditer(r"^([ \t]+)([\w']+)[ \t]*(?=:|\([^\n]*:)", clean[body_start:], re.M))
    if not matches: return []
    indent = min(len(m[1].expandtabs(8)) for m in matches)
    selected = [m for m in matches if len(m[1].expandtabs(8)) == indent]
    fields = []
    for i, match in enumerate(selected):
        start = body_start + match.start()
        end = body_start + selected[i+1].start() if i+1 < len(selected) else len(region)
        text = region[start:end]
        tags = cues(text)
        role = "field-role-unresolved"
        if match[2] in ("feasible", "successful", "reverting") or re.search(r"^\s*[\w\']+\s*:\s*(?:∃|(?:V2\.)?AllocatorWitness\b)", census.mask(text)):
            role = "explicit-witness-field-candidate"
        elif "∀" in census.mask(text): role = "universally-quantified-obligation-candidate"
        elif re.search(r"^\s*[\w\']+\s*:\s*[(⦃{].*?→",census.mask(text),re.S):
            role = "dependent-function-field-candidate"
        elif any(t in tags for t in ("execution-resolution", "representation", "equality-coherence")):
            role = "per-input-assertion-or-data-field-candidate"
        fields.append(dict(name=match[2],source=text,start=start,end=end,categories=tags,role=role))
    return fields

def classify(row, parsed_header=None):
    region = row["source_command_region"]
    clean = census.mask(region)
    end, body = prefix_end(clean,row["kind"])
    boundary = "source-delimiter-candidate"
    if end is None or end == len(clean):
        prefix, body = "", len(region)
        boundary = "unresolved; full original source region retained, proof not classified as header"
    else:
        prefix = region[:end]
    if parsed_header is not None:
        end = parsed_header["header_end"]
        prefix = region[:end]
        boundary = "Lean-parser source signature boundary; kernel/inferred signature pending"
    binders = outer_binders(prefix) if prefix else []
    fields = field_regions(region,body) if row["kind"] in ("structure","class") else []
    combined = "\n".join(b["type_source"] for b in binders)
    tags = cues(prefix if not fields else prefix+"\n"+"\n".join(f["source"] for f in fields))
    if fields:
        direct_input = any(re.match(r"^(?:(?:Solidity|Source|Evm)\.)*(?:State|EMState|Machine|Heap)\b",census.mask(b["type_source"]).strip()) and "→" not in census.mask(b["type_source"]) for b in binders)
        direct_input = direct_input or any({"before","after","hp","input","output"}.intersection(b["names"]) for b in binders)
        witness = any(f["role"] == "explicit-witness-field-candidate" for f in fields)
        uniform = any(f["role"] == "universally-quantified-obligation-candidate" for f in fields)
        input_carrier = any(re.match(r"^\s*[\w']+\s*:\s*(?:(?:Solidity|Source|Evm)\.)*(?:State|EMState|Machine|Heap)\b",census.mask(f["source"])) for f in fields)
        if not direct_input and input_carrier and any("representation" in f["categories"] for f in fields):
            bundle = "per-input-data-and-predicate-carrier-candidate"
        elif direct_input: bundle = "per-input-record-bundle-candidate"
        elif uniform and witness: bundle = "global-obligation-with-explicit-input-witness-candidate"
        elif uniform: bundle = "global-uniform-obligation-bundle-candidate"
        elif witness and "named-contract-record" in tags:
            bundle = "global-obligation-with-explicit-input-witness-candidate"
        elif any(f["role"] == "dependent-function-field-candidate" for f in fields):
            bundle = "global-dependent-function-bundle-candidate"
        else: bundle = "record-bundle-unresolved"
    elif row["kind"] in ("structure","class"):
        bundle = "record-bundle-unresolved"
    elif any("named-contract-record" in cues(b["type_source"]) for b in binders):
        bundle = "named-contract-and-input-bundle-candidate"
    elif binders: bundle = "per-input-binder-bundle-candidate"
    else: bundle = "no-header-binders-recognized-implicit-and-conclusion-premises-pending"
    return dict(bundle=bundle,basis="source syntax only; candidate labels are not Prop inference or satisfiability proofs",
        header_source=prefix,header_end=end,header_boundary_status=boundary,binders=binders,fields=fields,categories=tags,
        inherited_fields_pending=bool(re.search(r"\bextends\b",census.mask(prefix))),
        header_quantifiers_or_implications_present=("∀" in census.mask(prefix) or "→" in census.mask(prefix)),
        exact_signature_status="pending kernel elaboration including conclusion and section premises",
        field_census_status="own field source candidates only; inherited/default/implicit fields and exact types pending",
        joint_witness_status="pending; individual inhabitation never credits a simultaneous bundle",
        global_inhabitation_status="not established by source classification",
        per_input_feasibility_status="not established by global record existence")

def validate_parsed_headers(source, report):
    identities = {r["source_id"]:r for r in report["identities"]}
    if len(identities) != len(report["identities"]): raise ValueError("Duplicate header identity")
    result = {}
    seen = set()
    for header in report["results"]:
        index = header["source_id"]
        if index in seen or not 0 <= index < len(source["declarations"]): raise ValueError("Duplicate/invalid header source id")
        seen.add(index)
        row = source["declarations"][index]
        identity = identities.get(index)
        if identity is None or (identity["path"],identity["line"],identity["source_name"]) != (row["path"],row["line"],row["name"]):
            raise ValueError("Header source identity mismatch")
        if row["kind"] not in ("theorem","lemma"): raise ValueError("Header target is not a theorem")
        if header["status"] != "source-parsed": continue
        if header["syntax_kind"] != "Lean.Parser.Command.declSig": raise ValueError("Unexpected header syntax kind")
        region = row["source_command_region"]
        prefix = header["header_source"]
        if header["source_region_sha256"] != digest_text(region): raise ValueError("Header frozen source hash mismatch")
        if header["header_sha256"] != digest_text(prefix): raise ValueError("Header hash mismatch")
        end = header["header_end"]
        if not 0 < end < len(region) or prefix != region[:end]: raise ValueError("Header character span mismatch")
        if header["header_end_utf8"] != len(prefix.encode()): raise ValueError("Header UTF8 span mismatch")
        if not region[end:].lstrip().startswith((":=","|","where")): raise ValueError("Header does not precede proof delimiter")
        result[index] = header
    if seen != set(identities): raise ValueError("Header result inventory mismatch")
    expected = dict(requested=len(seen),source_parsed=len(result),parse_errors=len(seen)-len(result))
    if any(report["counts"].get(key) != value for key,value in expected.items()):
        raise ValueError("Header summary count mismatch")
    if report["counts"].get("kernel_signatures") != 0 or report["counts"].get("simultaneous_witness_credits") != 0:
        raise ValueError("Source parser cannot grant proof credits")
    return result

def digest_text(text):
    return hashlib.sha256(text.encode()).hexdigest()

def reconcile(root, source, routes, ownership, ownership_path, parsed_headers=None):
    items = {i["id"]: i for i in ownership["items"]}
    evidence_catalog = {}
    def evidence(ref):
        if "item" in ref:
            item = items[ref["item"]]
            text = json.dumps(item,ensure_ascii=False)
            location = str(ownership_path)+"#/items/"+ref["item"]
            evidence_catalog[location] = dict(source_sha256=sha(ownership_path),item=item)
        else:
            if "external_input" in ref:
                p = ownership_path.parent/ref["external_input"]
                location = str(p)
            else:
                p = root/ref["path"]
                location = ref["path"]
            text = p.read_text()
            evidence_catalog[location] = dict(source_sha256=sha(p))
        if ref.get("contains") and ref["contains"] not in text:
            raise ValueError("Evidence snippet absent: "+location+" : "+ref["contains"])
        return dict(location=location,**({"contains":ref["contains"]} if "contains" in ref else {}))
    def resolved(rule):
        for key in rule["owners"]+rule.get("discharger_owners",[]):
            if key not in ownership["ownerKeys"]: raise ValueError("Unknown owner key: "+key)
        return dict(area_owners=[dict(key=k,lane=ownership["ownerKeys"][k]) for k in rule["owners"]],
            obligations=rule["obligations"],evidence=[evidence(r) for r in rule["evidence"]],
            premise_dischargers=[dict(key=k,lane=ownership["ownerKeys"][k]) for k in rule.get("discharger_owners",[])],
            producer_status=rule.get("producer_status","declaration-specific boundary; no file ownership grant"),
            producer_lane_hint=rule.get("producer_lane_hint"),
            exact_live_file_owner_status="not confirmed; roadmap routing is not writer ownership",
            edit_authorization="none outside original audit scope")
    prepared = {r["id"]:resolved(r) for r in routes["rules"]}
    overrides = {(r["path"],r["short_name"]):resolved(r) for r in routes["declaration_overrides"]}
    used = collections.Counter()
    modules = []
    module_routes = {}
    for original in source["modules"]:
        path = original["path"]
        if sha(root/path) != original["sha256"]: raise ValueError("Frozen source hash mismatch: "+path)
        matches = [r for r in routes["rules"] if fnmatch.fnmatchcase(path,r["pattern"])]
        if not matches: raise ValueError("No area route: "+path)
        best = max(r["priority"] for r in matches)
        winners = [r for r in matches if r["priority"] == best]
        if len(winners) != 1: raise ValueError("Ambiguous route: "+path)
        rule = winners[0]
        module_routes[path] = prepared[rule["id"]]
        modules.append(dict(**original,area_route_rule=rule["id"],routing=module_routes[path]))
    rows = []
    parsed = validate_parsed_headers(source,parsed_headers) if parsed_headers is not None else {}
    for index, row in enumerate(source["declarations"]):
        key = (row["path"],row["name"].rsplit(".",1)[-1])
        override = overrides.get(key)
        if override: used[key] += 1
        raw = (root/row["path"]).read_text()[row["source_start"]:row["source_end"]]
        if raw != row["source_command_region"]: raise ValueError("Source span mismatch")
        rows.append(dict(**row,area_routing=override or module_routes[row["path"]],
            declaration_owner_override=bool(override),premise_bundle=classify(row,parsed.get(index)),
            parser_header_status="source-parsed" if index in parsed else "not supplied; lexical candidate only"))
    if any(used[k] != 1 for k in overrides): raise ValueError("Override not used exactly once")
    identities = [(r["path"],r["line"],r["name"]) for r in rows]
    if len(identities) != len(set(identities)): raise ValueError("Duplicate source identity")
    count = collections.Counter(r["premise_bundle"]["bundle"] for r in rows)
    owner_count = collections.Counter("+".join(o["key"] for o in r["area_routing"]["area_owners"]) for r in rows)
    return dict(base=source["base"],boundary=routes["boundary"],modules=modules,declarations=rows,
        evidence_catalog=evidence_catalog,
        counts=dict(source["counts"],area_routed_declarations=len(rows),
            source_field_candidates=sum(len(r["premise_bundle"]["fields"]) for r in rows),
            source_header_binders=sum(len(r["premise_bundle"]["binders"]) for r in rows),
            parser_source_signatures=len(parsed),
            unresolved_source_headers=sum(not r["premise_bundle"]["header_source"] for r in rows),
            bundle_classes=dict(sorted(count.items())),area_owner_routes=dict(sorted(owner_count.items())),
            exact_live_file_owner_confirmations=0,kernel_verified_signatures=0,
            public_compiler_contract_credits=0),
        fixture_boundary="EntryAudit remains a local fixture only; no new census/public-contract witness credits")

def attach_findings(root, result, source_findings):
    entries, seen = [], set()
    for finding in source_findings["findings"]:
        name = finding["qualified_statement"]
        if name in seen: raise ValueError("Duplicate escalation statement: "+name)
        seen.add(name)
        parents = [r for r in result["declarations"] if r["path"] == finding["path"] and r["name"] == finding["parent_source_name"]]
        if len(parents) != 1: raise ValueError("Finding parent not unique")
        fields = [f for f in parents[0]["premise_bundle"]["fields"] if f["name"] == finding["field_name"]]
        if len(fields) != 1 or finding["field_contains"] not in fields[0]["source"]:
            raise ValueError("Finding field evidence missing")
        if len(finding["repair_options"]) not in (2,3): raise ValueError("Repair options required")
        if finding["repair_authorization"] != "none": raise ValueError("No repair permission inferred")
        evidence = []
        for ref in finding["evidence"]:
            path = root/ref["path"]
            if ref["contains"] not in path.read_text(): raise ValueError("Finding source evidence absent")
            evidence.append(dict(**ref,sha256=sha(path)))
        entries.append(dict(**{k:v for k,v in finding.items() if k != "evidence"},evidence=evidence))
    result["source_findings"] = entries
    result["counts"]["escalation_statements"] = len(entries)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root",type=pathlib.Path,default=pathlib.Path.cwd())
    p.add_argument("--census",type=pathlib.Path,required=True)
    p.add_argument("--owners",type=pathlib.Path,required=True)
    p.add_argument("--routes",type=pathlib.Path,required=True)
    p.add_argument("--output",type=pathlib.Path,required=True)
    p.add_argument("--parsed-headers",type=pathlib.Path)
    p.add_argument("--findings",type=pathlib.Path)
    p.add_argument("--escalations",type=pathlib.Path)
    p.add_argument("--uncovered",type=pathlib.Path)
    a = p.parse_args()
    result = reconcile(a.root.resolve(),json.loads(a.census.read_text()),json.loads(a.routes.read_text()),json.loads(a.owners.read_text()),a.owners.resolve(),json.loads(a.parsed_headers.read_text()) if a.parsed_headers else None)
    if a.findings:
        attach_findings(a.root.resolve(),result,json.loads(a.findings.read_text()))
    result["input_sha256"] = {str(v.resolve()):sha(v) for v in (a.census,a.owners,a.routes)}
    if a.parsed_headers: result["input_sha256"][str(a.parsed_headers.resolve())] = sha(a.parsed_headers)
    if a.findings: result["input_sha256"][str(a.findings.resolve())] = sha(a.findings)
    if a.escalations:
        lines = ["ESCALATE: "+f["qualified_statement"]+"; evidence: "+f["finding"]+" Sources: "+", ".join(e["path"] for e in f["evidence"])+"; options: "+" | ".join(f["repair_options"]) for f in result.get("source_findings",[])]
        a.escalations.parent.mkdir(parents=True,exist_ok=True)
        a.escalations.write_text("\n".join(lines)+("\n" if lines else ""))
    if a.uncovered:
        lines = ["source_path\tline\tsource_spelling_not_kernel_FQN\tarea_owner_keys\tbundle_candidate\tstatus"]
        for r in result["declarations"]:
            lines.append("\t".join([r["path"],str(r["line"]),r["name"],"+".join(o["key"] for o in r["area_routing"]["area_owners"]),r["premise_bundle"]["bundle"],"kernel-signature-and-simultaneous-witness-pending"]))
        a.uncovered.parent.mkdir(parents=True,exist_ok=True)
        a.uncovered.write_text("\n".join(lines)+"\n")
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    print(json.dumps(dict(counts=result["counts"],sha256=sha(a.output)),indent=2))

if __name__ == "__main__": main()
