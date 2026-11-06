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
    for field in row.get("fields", []):
        text = source[field["start"]:field["end"]]
        assert text == field["source"]
        assert hashlib.sha256(text.encode()).hexdigest() == field["sha256"]
        assert field["end"] <= len(source)
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
