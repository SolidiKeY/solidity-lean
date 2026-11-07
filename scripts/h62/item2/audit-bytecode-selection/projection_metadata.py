"""Guard projection-registry observations from becoming inherited/source proofs."""
import json
import re
import kernel_metadata as metadata

RECORD_FIELDS={"fingerprint","name","module","private","type_expr","level_params",
               "metadata_status","registry","constructor","inductive","structure"}
STATUSES={"no_registered_projection","constructor_metadata_unavailable",
          "inductive_metadata_unavailable","structure_metadata_unavailable",
          "registered_projection_observed"}

def _text(value):
    if not isinstance(value,str) or not value:
        raise ValueError("missing projection text")

def _levels(value):
    if (not isinstance(value,list) or any(not isinstance(x,str) or not x for x in value)
            or len(value)!=len(set(value))):
        raise ValueError("invalid projection universes")

def _nat(value):
    if type(value) is not int or value<0:
        raise ValueError("invalid projection numeric metadata")

def validate_projection(row, pins):
    if not isinstance(row,dict) or set(row)!=RECORD_FIELDS:
        raise ValueError("projection record schema differs")
    if row["fingerprint"]!=pins["fingerprint"]:
        raise ValueError("projection fingerprint differs")
    _text(row["name"])
    target=pins["targets"].get(row["name"])
    if target is None:
        raise ValueError("projection outside requested roster")
    for key in ["module","type_expr"]:
        if not isinstance(row[key],str) or row[key]!=target[key]:
            raise ValueError("projection type/module differs")
    if type(row["private"]) is not bool or row["private"] is not target["private"]:
        raise ValueError("projection private flag differs")
    _levels(row["level_params"])
    if row["level_params"]!=target["level_params"]:
        raise ValueError("projection universes differ")
    status=row["metadata_status"]
    if not isinstance(status,str) or status not in STATUSES:
        raise ValueError("unknown projection status")
    registry,ctor,inductive,structure=(row[k] for k in ["registry","constructor","inductive","structure"])
    if registry is None:
        if status!="no_registered_projection" or any(v is not None for v in [ctor,inductive,structure]):
            raise ValueError("missing registry contradicts metadata status")
        return
    if not isinstance(registry,dict) or set(registry)!={"ctor_name","num_params","field_index","from_class"}:
        raise ValueError("invalid registry schema")
    _text(registry["ctor_name"]);_nat(registry["num_params"]);_nat(registry["field_index"])
    if type(registry["from_class"]) is not bool:
        raise ValueError("invalid projection class flag")
    if ctor is None:
        if status!="constructor_metadata_unavailable" or inductive is not None or structure is not None:
            raise ValueError("missing constructor contradicts status")
        return
    if (not isinstance(ctor,dict) or set(ctor)!={"name","type_expr","level_params","inductive","num_params","num_fields","constructor_index"}
            or ctor["name"]!=registry["ctor_name"]):
        raise ValueError("constructor identity/schema differs")
    for key in ["name","type_expr","inductive"]:_text(ctor[key])
    _levels(ctor["level_params"])
    for key in ["num_params","num_fields","constructor_index"]:_nat(ctor[key])
    if inductive is None:
        if status!="inductive_metadata_unavailable" or structure is not None:
            raise ValueError("missing inductive contradicts status")
        return
    if (not isinstance(inductive,dict) or set(inductive)!={"name","type_expr","level_params"}
            or inductive["name"]!=ctor["inductive"]):
        raise ValueError("inductive identity/schema differs")
    _text(inductive["name"]);_text(inductive["type_expr"]);_levels(inductive["level_params"])
    if structure is None:
        if status!="structure_metadata_unavailable":
            raise ValueError("missing structure contradicts status")
        return
    if (status!="registered_projection_observed" or not isinstance(structure,dict)
            or set(structure)!={"name","projections","parents"} or structure["name"]!=inductive["name"]):
        raise ValueError("structure identity/schema differs")
    if not isinstance(structure["projections"],list) or not isinstance(structure["parents"],list):
        raise ValueError("invalid structure lists")
    for name in structure["projections"]:_text(name)
    if len(set(structure["projections"]))!=len(structure["projections"]):
        raise ValueError("duplicate structure projection")
    for parent in structure["parents"]:
        if not isinstance(parent,dict) or set(parent)!={"structure","projection","subobject"}:
            raise ValueError("invalid structure parent schema")
        _text(parent["structure"]);_text(parent["projection"])
        if type(parent["subobject"]) is not bool:
            raise ValueError("invalid parent subobject flag")
    if len({p["projection"] for p in structure["parents"]})!=len(structure["parents"]):
        raise ValueError("duplicate structure parent")

def read_projection_records(log, pins):
    """Parse a complete supplement; receipt/kernel validation stays with caller."""
    if (not isinstance(pins,dict) or not isinstance(pins.get("fingerprint"),str)
            or re.fullmatch(r"[0-9a-f]{64}",pins["fingerprint"]) is None
            or not isinstance(pins.get("targets"),dict) or not pins["targets"]):
        raise ValueError("invalid projection pins")
    rows={};done=None
    for line in log.splitlines():
        if not line.strip():continue
        if done is not None:
            raise ValueError("projection output after completion")
        if line.startswith("H62_PROJECTION_JSON "):
            row=metadata.parse_json(line.removeprefix("H62_PROJECTION_JSON "));validate_projection(row,pins)
            if row["name"] in rows:raise ValueError("duplicate projection record")
            rows[row["name"]]=row
        elif line.startswith("H62_PROJECTION_DONE "):
            done=metadata.parse_json(line.removeprefix("H62_PROJECTION_DONE "))
        else:raise ValueError("unexpected projection diagnostic")
    if (not isinstance(done,dict) or set(done)!={"fingerprint","count"}
            or done["fingerprint"]!=pins["fingerprint"] or type(done["count"]) is not int
            or done["count"]!=len(pins["targets"]) or set(rows)!=set(pins["targets"])):
        raise ValueError("incomplete projection supplement")
    records=[rows[name] for name in sorted(rows)]
    relations=[]
    for row in records:
        registry,ctor,structure=(row[k] for k in ["registry","constructor","structure"])
        relations.append({"name":row["name"],
            "registered_parameter_counts_match":None if registry is None or ctor is None else registry["num_params"]==ctor["num_params"],
            "registered_index_within_constructor":None if registry is None or ctor is None else registry["field_index"]<ctor["num_fields"],
            "listed_structure_projection":None if structure is None else row["name"] in structure["projections"],
            "instantiated_inherited_type_accepted":False,"source_ownership_established":False,"joint_witness_established":False})
    return {"records":records,"observed_relations":relations,"inherited_instantiation_accepted":False,
            "source_correspondence_established":False,"global_witness_ledger_linked":False,
            "boundary":"Supplemental registry/constructor observations only; no parameter substitution, inherited-field proof, source/producer ownership, feasibility or full census acceptance."}


def registry_graph(rows, log, pins):
    """Join observed registry facts without counting inherited routes as proofs.

    Guards regression: repeated parent routes must not multiply one field into
    several discharged obligations, or hide unavailable parent/field records.
    Actual native provenance and kernel acceptance remain caller obligations.
    """
    import copy
    metadata.validate_rows(rows)
    by_name = {row["name"]: row for row in rows}
    fields = {row["name"]: row for row in rows if row["is_projection"]}
    packet = read_projection_records(log, pins)
    if set(pins["targets"]) != set(fields):
        raise ValueError("registry join must retain every supplied projection")
    canonical = lambda value: json.dumps(value, sort_keys=True, separators=(",", ":"))
    for name, target in pins["targets"].items():
        if canonical(target) != canonical(metadata.observed_type(fields[name])):
            raise ValueError("registry target differs from supplied kernel snapshot")
    observed = {row["name"]: row for row in packet["records"]}
    structures = {}
    for row in packet["records"]:
        structure = row["structure"]
        if structure is None:
            continue
        name = structure["name"]
        snapshot = {key: row[key] for key in ("constructor", "inductive", "structure")}
        if name in structures and canonical(structures[name]) != canonical(snapshot):
            raise ValueError("conflicting observations of one structure")
        structures[name] = snapshot
    nodes = []
    for row in packet["records"]:
        name = row["name"]
        nodes.append({"name": name, "kernel_type": metadata.observed_type(fields[name]),
                      "registry": row["registry"], "metadata_status": row["metadata_status"],
                      "structure": None if row["structure"] is None else row["structure"]["name"],
                      "proof_type": fields[name]["proof_type"],
                      "inherited_instantiation_accepted": False, "joint_witness_established": False})
    indexes = []
    for root in sorted(structures):
        routes = {}; edges = []; missing = []; cycles = []
        def walk(name, trail):
            if name in trail:
                cycles.append(trail + [name]); return
            trail = trail + [name]
            snapshot = structures.get(name)
            if snapshot is None:
                missing.append({"kind": "structure", "name": name, "route": trail}); return
            structure = snapshot["structure"]
            for field in structure["projections"]:
                record = observed.get(field)
                same_owner = record is not None and record["structure"] is not None and record["structure"]["name"] == name
                if same_owner:
                    routes.setdefault(field, []).append(trail)
                else:
                    missing.append({"kind": "field", "name": field, "route": trail,
                                    "kernel_record_present": field in by_name,
                                    "registry_observation_present": record is not None,
                                    "observed_owner_matches": False})
            for parent in structure["parents"]:
                projection = observed.get(parent["projection"])
                edge = dict(parent, child=name, route=trail + [parent["structure"]],
                            projection_kernel_record_present=parent["projection"] in by_name,
                            projection_registry_present=projection is not None,
                            projection_owner_matches=projection is not None and projection["structure"] is not None and projection["structure"]["name"] == name,
                            parent_structure_observed=parent["structure"] in structures,
                            instantiated_type_checked=False)
                edges.append(edge)
                walk(parent["structure"], trail)
        walk(root, [])
        indexes.append({"root": root, "fields": [{"name": name, "routes": routes[name]} for name in sorted(routes)],
                        "observed_unique_fields": len(routes), "edges": edges, "missing": missing, "cycles": cycles,
                        "inherited_instantiation_accepted": False, "source_correspondence_established": False,
                        "joint_witnesses_established": 0})
    return copy.deepcopy({"kernel_record_count": len(rows), "projection_record_count": len(fields),
                          "nonprojection_records": sorted(set(by_name) - set(fields)),
                          "nodes": nodes, "structures": indexes,
                          "source_correspondence_established": False, "source_ownership_established": False,
                          "inherited_instantiation_accepted": False, "global_witness_ledger_linked": False,
                          "full_census_accepted": False,
                          "boundary": "Exact supplied snapshot join and observed parent routes only; no instantiated field types, provenance, witness or source correspondence accepted."})
