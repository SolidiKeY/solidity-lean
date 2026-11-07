#!/usr/bin/env python3
"""Independent artifact consistency checks; does not elaborate Lean."""
import argparse
import collections
import hashlib
import json
import pathlib
import re

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("--repo", required=True, type=pathlib.Path)
p.add_argument("--inventory", required=True, type=pathlib.Path)
p.add_argument("--dependencies", type=pathlib.Path)
a = p.parse_args()
j = json.loads(a.inventory.read_text())
assert hashlib.sha256((a.repo/j["scope"]).read_bytes()).hexdigest() == j["map_sha256"]
module_paths = set()
for m in j["modules"] + j["supplemental_modules"]:
    raw = (a.repo/m["path"]).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == m["sha256"], m["path"]
    assert m["path"] not in module_paths
    module_paths.add(m["path"])
seen = set()
for row in j["theorems"] + j["structures"] + j["supplemental_structures"] + j["supplemental_theorems"]:
    source = (a.repo/row["path"]).read_text()
    key = (row["path"], row["start"])
    assert key not in seen, key
    seen.add(key)
    sig = source[row["start"]:row["end"]]
    assert sig == row["signature_source"]
    assert hashlib.sha256(sig.encode()).hexdigest() == row["signature_sha256"]
    assert hashlib.sha256(source[:row["start"]].encode()).hexdigest() == row["source_prefix_sha256"]
    if "contract_source" in row:
        contract = source[row["start"]:row["contract_end"]]
        assert contract == row["contract_source"]
        assert hashlib.sha256(contract.encode()).hexdigest() == row["contract_sha256"]
    assert row["statement_fidelity"] == "pending-elaboration"
    assert row["simultaneous_witness"] == "pending"
    if row["terminator"] == "equations":
        assert source[row["end"]] == "|"
    else:
        assert source.startswith(row["terminator"], row["end"])
    for ctx in row["context_commands"]:
        assert source[ctx["start"]:ctx["end"]] == ctx["source"]
        assert ctx["end"] <= row["start"]
    field_keys = set()
    for field in row.get("fields", []):
        text = source[field["start"]:field["end"]]
        assert text == field["source"]
        assert hashlib.sha256(text.encode()).hexdigest() == field["sha256"]
        assert field["end"] <= len(source)
        assert (field["start"], field["end"]) not in field_keys
        field_keys.add((field["start"], field["end"]))
        assert re.match(r"\s*([A-Za-z_][A-Za-z0-9_']*)\s*:", text)[1] == field["source_qualified_name"].rsplit(".",1)[-1]
# Independent line-oriented count for this frozen tree; regex never extracts a
# signature, so it cannot duplicate the generator's signature-boundary algorithm.
counts = {}
for m in j["modules"]:
    source = (a.repo/m["path"]).read_text()
    counts[m["path"]] = len(re.findall(r"^(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+", source, re.M))
actual = collections.Counter(row["path"] for row in j["theorems"])
assert all(actual[path] == count for path, count in counts.items())
assert sum(counts.values()) == j["theorem_count"] == 968
assert len(j["modules"]) == 162
assert len(j["structures"]) == 7
assert sum(len(r["fields"]) for r in j["structures"]) == 32
by_name = {r["source_qualified_name"]: r for r in j["structures"]}
# Regression for confirmed review bug: following declaration docs must not
# become part of a field's signature.
for name in ("Solidity.Lowering.V07.ContextMap", "Solidity.Lowering.V07.P12NextInterface.Condition"):
    assert "/--" not in by_name[name]["fields"][-1]["source"]
producer_rows = [r for r in j["theorems"] if any(b["category"] == "global-producer-contract" for b in r["binder_evidence"])]
assert len(producer_rows) == 15
for suffix in ("scalar_value", "source_assignment_run"):
    assert any(r["local_name"] == suffix for r in producer_rows)
print("PASS: 162 source hashes; 968 unique theorem slices; 7 mapped structures / 32 fields; exact context offsets; 15 explicit global-producer signatures; field-boundary regressions")
print("NOT CHECKED: Lean elaboration, propositionhood, semantic premise completeness, inhabitation, simultaneous witnesses, public-contract success")

if a.dependencies:
    d = json.loads(a.dependencies.read_text())
    seen = set()
    for contract in d["contracts"]:
        raw = (a.repo/contract["path"]).read_bytes()
        source = raw.decode()
        assert hashlib.sha256(raw).hexdigest() == contract["module_sha256"]
        assert source[contract["start"]:contract["end"]] == contract["source"]
        assert source[contract["start"]:contract["header_end"]] == contract["header_source"]
        assert hashlib.sha256(contract["source"].encode()).hexdigest() == contract["sha256"]
        assert contract["name"] not in seen
        seen.add(contract["name"])
        assert contract["inhabitation"] == "unproved"
        assert contract["statement_fidelity"] == "pending-elaboration"
        field_names = set()
        for field in contract.get("fields", []):
            assert contract["start"] <= field["start"] < field["end"] <= contract["end"]
            assert source[field["start"]:field["end"]] == field["source"]
            assert hashlib.sha256(field["source"].encode()).hexdigest() == field["sha256"]
            assert re.match(r"\s*([A-Za-z_][A-Za-z0-9_']*)\s*:",field["source"])[1] == field["name"]
            assert field["name"] not in field_names
            field_names.add(field["name"])
    assert len(d["contracts"]) == d["count"] == 17
    assert sum(len(c.get("fields", [])) for c in d["contracts"]) == d["fields"] == 82
    print("PASS: 17 imported contract definitions / 82 fields; exact source/hash/offset checks; inhabitation remains unproved")
