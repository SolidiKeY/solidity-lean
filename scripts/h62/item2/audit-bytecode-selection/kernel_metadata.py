"""Guard regression: incomplete metadata must not become source identity or coverage."""
import json
import hashlib
import re
from collections import Counter, defaultdict

FIELDS = {
    "manifest_sha256", "name", "user_name", "private", "original_kind",
    "declaration_range", "module", "kind", "interface_or_premises_module",
    "predicate_valued", "body_expr", "body_status", "is_theorem",
    "is_projection", "proof_type", "type_expr", "type", "level_params",
    "binders", "parents",
}

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key: " + key)
        result[key] = value
    return result

def parse_json(value):
    return json.loads(value, object_pairs_hook=unique_object)

def text(value):
    return isinstance(value, str) and bool(value)

def validate_record(row):
    if not isinstance(row, dict) or set(row) != FIELDS:
        raise ValueError("record schema differs")
    for key in ("manifest_sha256", "name", "user_name", "module", "type_expr", "type", "body_status"):
        if not text(row[key]):
            raise ValueError("missing record text: " + key)
    for key in ("private", "interface_or_premises_module", "predicate_valued",
                "is_theorem", "is_projection", "proof_type"):
        if type(row[key]) is not bool:
            raise ValueError("record flag is not Boolean: " + key)
    kinds = {"Lean.ConstantKind." + name for name in
             ("defn", "thm", "axiom", "opaque", "quot", "induct", "ctor", "recursor")}
    if row["original_kind"] is not None and row["original_kind"] not in kinds:
        raise ValueError("unsupported original constant kind")
    if row["is_theorem"] != (row["original_kind"] == "Lean.ConstantKind.thm"):
        raise ValueError("original theorem kind contradicts flag")
    if row["body_expr"] == "":
        raise ValueError("empty body expression")
    expected = "field" if row["is_projection"] else "theorem" if row["is_theorem"] else "constant"
    if row["kind"] != expected:
        raise ValueError("record kind contradicts flags")
    for key in ("original_kind", "body_expr"):
        if row[key] is not None and not isinstance(row[key], str):
            raise ValueError("invalid optional expression/kind")
    if row["is_theorem"] and not row["proof_type"]:
        raise ValueError("theorem type is not a proposition")
    if row["is_theorem"] and row["body_expr"] is not None:
        raise ValueError("unexpected theorem proof body")
    expected_body_status = ("proof body intentionally omitted" if row["is_theorem"] else
                            "available expression; not unfolded dependency closure" if row["body_expr"] is not None else
                            "no available value")
    if row["body_status"] != expected_body_status:
        raise ValueError("body availability contradicts record")
    if row["interface_or_premises_module"] != ("Interface" in row["module"] or "Premises" in row["module"]):
        raise ValueError("module classification contradicts origin")
    span = row["declaration_range"]
    if span is not None:
        if not isinstance(span, dict) or set(span) != {"start_line", "end_line", "selection_line"}:
            raise ValueError("invalid declaration range")
        if any(type(value) is not int for value in span.values()):
            raise ValueError("noninteger declaration range")
        if not 1 <= span["start_line"] <= span["selection_line"] <= span["end_line"]:
            raise ValueError("inconsistent declaration range")
    if not isinstance(row["level_params"], list) or any(not isinstance(x, str) for x in row["level_params"]):
        raise ValueError("invalid universe parameters")
    if len(set(row["level_params"])) != len(row["level_params"]):
        raise ValueError("duplicate universe parameter")
    if not isinstance(row["binders"], list) or not isinstance(row["parents"], list):
        raise ValueError("invalid binder/parent lists")
    for binder in row["binders"]:
        if not isinstance(binder, dict) or set(binder) != {"name", "binder_info", "type", "proof_binder", "head_constant"}:
            raise ValueError("binder schema differs")
        if any(not isinstance(binder[k], str) for k in ("name", "binder_info", "type")):
            raise ValueError("invalid binder text")
        if binder["binder_info"] not in {"Lean.BinderInfo." + name for name in
                                          ("default", "implicit", "strictImplicit", "instImplicit")}:
            raise ValueError("unsupported binder kind")
        if type(binder["proof_binder"]) is not bool:
            raise ValueError("invalid binder proof flag")
        if binder["head_constant"] is not None and not text(binder["head_constant"]):
            raise ValueError("invalid binder head constant")
    for parent in row["parents"]:
        if not isinstance(parent, dict) or set(parent) != {"structure", "projection", "subobject"}:
            raise ValueError("parent schema differs")
        if not text(parent["structure"]) or not text(parent["projection"]) or type(parent["subobject"]) is not bool:
            raise ValueError("invalid parent metadata")
    if len({p["projection"] for p in row["parents"]}) != len(row["parents"]):
        raise ValueError("duplicate parent projection")
    return row

def read_records(log, pins):
    rows, done = [], None
    for line in log.splitlines():
        if line.startswith("H62_CENSUS_JSON "):
            if done is not None:
                raise ValueError("record after completion")
            rows.append(validate_record(parse_json(line[len("H62_CENSUS_JSON "):])))
        elif line.startswith("H62_CENSUS_DONE "):
            if done is not None:
                raise ValueError("duplicate completion")
            done = parse_json(line[len("H62_CENSUS_DONE "):])
        elif re.search(r"(?:^|:\d+:\d+: )(?:error|warning)(?:\([^)]*\))?:", line):
            raise ValueError("inspection diagnostic")
    if not rows:
        raise ValueError("empty inspection is not package evidence")
    if done is None or not isinstance(done, dict) or set(done) != {"manifest_sha256", "counts"}:
        raise ValueError("missing valid completion")
    if done["manifest_sha256"] != pins["manifest_sha256"]:
        raise ValueError("completion fingerprint differs")
    if any(row["manifest_sha256"] != pins["manifest_sha256"] for row in rows):
        raise ValueError("record fingerprint differs")
    counts = Counter(row["module"] for row in rows)
    expected = {module: counts[module] for module in pins["modules"]}
    if done["counts"] != expected or set(counts) - set(expected):
        raise ValueError("completion membership/counts differ")
    if not isinstance(done["counts"], dict) or any(type(v) is not int or v < 0 for v in done["counts"].values()):
        raise ValueError("invalid completion counts")
    if len({row["name"] for row in rows}) != len(rows):
        raise ValueError("duplicate kernel identity")
    return rows

def validate_rows(rows):
    for row in rows:
        validate_record(row)
    if len({row["name"] for row in rows}) != len(rows):
        raise ValueError("duplicate kernel identity")
    if len({row["manifest_sha256"] for row in rows}) > 1:
        raise ValueError("mixed inspection fingerprints")


def source_links(rows, source_rows, private_ids):
    """Return candidate name/range matches; execution provenance is not checked here."""
    validate_rows(rows)
    if not isinstance(private_ids, (set, frozenset)) or any(not text(i) for i in private_ids):
        raise ValueError("invalid private source identities")
    ids = [source.get("id") for source in source_rows]
    if any(not text(i) for i in ids) or len(set(ids)) != len(ids):
        raise ValueError("duplicate or invalid source identity")
    for source in source_rows:
        for key in ("module", "candidate_user_name"):
            if not text(source.get(key)):
                raise ValueError("invalid source key")
        line=source.get("name_token_line")
        if line is not None and (type(line) is not int or line < 1):
            raise ValueError("invalid source name line")
        if not re.fullmatch(r"[a-f0-9]{64}",source.get("signature_sha256","")):
            raise ValueError("invalid source signature hash")
    index = defaultdict(list)
    for row in rows:
        span = row["declaration_range"]
        if row["is_theorem"] and span is not None:
            index[(row["module"], row["user_name"], span["selection_line"])].append(row)
    source_counts=Counter((s["module"],s["candidate_user_name"],s["name_token_line"],
                           s["id"] in private_ids) for s in source_rows)
    results = []
    for source in source_rows:
        key = (source["module"], source["candidate_user_name"], source["name_token_line"])
        candidates = index[key]
        exact = [row for row in candidates if row["private"] == (source["id"] in private_ids)]
        ambiguous=source_counts[(*key,source["id"] in private_ids)] != 1 or len(exact)>1
        status = "ambiguous" if ambiguous else "name_range_match_candidate" if len(exact)==1 else "unmatched"
        results.append({
            "source_id": source["id"], "source_signature_sha256": source["signature_sha256"],
            "kernel_names": [row["name"] for row in exact],
            "kernel_record_sha256": [hashlib.sha256(json.dumps(row,sort_keys=True,separators=(",",":")).encode()).hexdigest() for row in exact],
            "kernel_type_expr_sha256": [hashlib.sha256(row["type_expr"].encode()).hexdigest() for row in exact],
            "status": status,
            "statement_correspondence": "not established by name/range identity",
            "witness_status": "uncovered; identity never establishes joint feasibility",
        })
    return results

def observed_type(row):
    """Retain supplied type evidence, not kernel execution or type correspondence.

    In particular a projection name does not establish its domain, codomain,
    universe instantiation, or ownership by the purported child structure.
    """
    validate_record(row)
    encoded = json.dumps(row, sort_keys=True, separators=(",", ":")).encode()
    # A snapshot must not retain mutable aliases to caller-owned metadata.
    row = json.loads(encoded)
    return {
        "name": row["name"], "module": row["module"],
        "private": row["private"], "declaration_range": row["declaration_range"],
        "manifest_sha256": row["manifest_sha256"],
        "record_sha256": hashlib.sha256(encoded).hexdigest(),
        "type_expr": row["type_expr"], "type": row["type"],
        "type_expr_sha256": hashlib.sha256(row["type_expr"].encode()).hexdigest(),
        "level_params": row["level_params"], "binders": row["binders"],
        "proof_type": row["proof_type"], "predicate_valued": row["predicate_valued"],
        "status": "observed input record only; no provenance or instantiated type acceptance",
    }


def parent_metadata(rows):
    """Preserve exact observed edges/routes; no instantiated inherited proof follows."""
    validate_rows(rows)
    by_name = {row["name"]: row for row in rows}
    if len(by_name) != len(rows):
        raise ValueError("duplicate kernel identity")
    results = []
    for root in rows:
        if not root["parents"]:
            continue
        edges, unresolved, cycles = [], [], []
        def walk(row, trail):
            if row["name"] in trail:
                cycles.append(trail + [row["name"]])
                return
            trail = trail + [row["name"]]
            for parent in row["parents"]:
                target = by_name.get(parent["structure"])
                projection = by_name.get(parent["projection"])
                edge = dict(parent, child=row["name"], route=trail + [parent["structure"]],
                            parent_record_present=target is not None,
                            projection_record_present=projection is not None,
                            projection_kind=projection["kind"] if projection is not None else None,
                            child_type=observed_type(row),
                            parent_type=observed_type(target) if target is not None else None,
                            projection_type=observed_type(projection) if projection is not None else None)
                edges.append(edge)
                if target is None or projection is None:
                    unresolved.append(edge)
                if projection is not None and not projection["is_projection"]:
                    raise ValueError("parent metadata points to nonprojection")
                if target is not None:
                    walk(target, trail)
        walk(root, [])
        results.append({"root": root["name"], "edges": edges, "missing_records": unresolved,
                        "cycles": cycles,
                        "edge_relationship_status": "observed names and supplied types only; structure ownership and instantiated projection types not checked",
                        "inherited_obligation_status": "uncovered; instantiated inherited types not reconstructed",
                        "witness_status": "uncovered"})
    return results
