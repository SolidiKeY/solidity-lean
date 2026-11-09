#!/usr/bin/env python3
"""Validate provisional source evidence; full completion is fail-closed."""
import argparse
import hashlib
import json
import re
from pathlib import Path
from census import generate

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("--evidence", type=Path, default=Path("/workspace/h62-audit-evidence"))
p.add_argument("--require-complete", action="store_true")
a = p.parse_args()
if not __debug__: raise SystemExit("optimized Python disables checks; refused")
root = Path.cwd()
source = json.loads((a.evidence/"source-census.json").read_text())
assert source == generate(root), "census differs from frozen-source regeneration"
ledger = json.loads((root/"tests/h62/item2/audit-exact-verification/witness-ledger.json").read_text())
rows = {r["id"]:r for r in source["declarations"]}
assert len({e["original"] for e in ledger["entries"]}) == len(ledger["entries"])
receipt = json.loads((a.evidence/ledger["proof_receipt"]).read_text())
hashfile = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert receipt["runner_sha256"] == hashfile(root/"scripts/h62/item2/audit-exact-verification/bounded-check.sh")
assert receipt["proof_file"] == ledger["proof_file"]
assert receipt["log"] == ledger["proof_log"]
assert receipt["proof_sha256"] == hashfile(root/ledger["proof_file"]), "stale proof evidence"
assert receipt["interface_sha256"] == hashfile(root/receipt["interface_file"])
assert receipt["log_sha256"] == hashfile(a.evidence/receipt["log"])
assert receipt["exit"] == 0 and (a.evidence/"bounded-audit.exit").read_text().strip() == "0"
assert receipt["toolchain"] == "leanprover/lean4:v4.35.0"
log = (a.evidence/ledger["proof_log"]).read_text()
assert "AUDIT_PASS " in log and log.endswith("COMPLETED audit\n"), "incomplete proof run"
axioms = re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^]]*)\])", log)
seen = set()
for name, _, values in axioms:
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    assert not values or set(values.split(", ")) <= allowed, (name, values)
    seen.add(name)
for e in ledger["entries"]:
    r = rows[e["source_id"]]
    assert r["name_candidate"] == e["original"]
    assert r["source_signature_sha256"] == e["source_signature_sha256"]
    assert e["helper"] in seen, e["helper"]
    assert "@"+e["original"].removeprefix("Solidity.Linear.")+" :" in log, e["original"]
expected = {e["helper"] for e in ledger["entries"]} | {
    "Solidity.H62.ExactAudit.VisitedSet."+name for name in
    ("supported_node_closes", "reject_all_does_not_close", "zero_fuel_is_out")}
assert seen == expected, "missing/unexpected helper/control axiom evidence"
proof = (root/ledger["proof_file"]).read_text()
assert not re.search(r"\b(sorry|axiom|native_decide|unsafe|implemented_by|maxHeartbeats)\b", proof)
count = len(rows)-len(ledger["entries"])
print(json.dumps({"source_validation":"pass", "modules":source["counts"]["modules"],
    "source_candidates":len(rows), "local_bundles":len(ledger["entries"]),
    "uncovered_source_candidates":count, "full_interface_census":"pending_elaboration_and_owners",
    "assignment_status":"blocked"}))
if a.require_complete:
    print("FULL_AUDIT_GATE_FAIL: exact interface census, remaining witnesses, compiler totality and final gates incomplete")
    raise SystemExit(1)
