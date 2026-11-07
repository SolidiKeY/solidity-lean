#!/usr/bin/env python3
"""Reconcile exact source signatures, target IDs and checked telescope witnesses.
This is a partial witness census; it fails closed on stale or missing evidence.
"""
import argparse
import hashlib
import json
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("--census", type=Path, required=True)
p.add_argument("--checks", type=Path, required=True)
p.add_argument("--output", type=Path, required=True)
p.add_argument("--gate-repair-manifest", type=Path)
args = p.parse_args()
root = Path(__file__).resolve().parents[4]
census = json.loads(args.census.read_text())
index = json.loads((root / "tests/h62/item2/audit-language/witness-index.json").read_text())
checks = json.loads(args.checks.read_text())
revisions = {}
if args.gate_repair_manifest:
    from gate_repair import approved_revisions
    revisions = approved_revisions(args.gate_repair_manifest)
by_id = {d["id"]: d for d in census["declarations"]}
assert len(by_id) == len(census["declarations"])
assert not census["scan_errors"] and not census["unresolved_references"]
assert len({r["target"] for r in index}) == len(index)
by_file = {r["file"]: r for r in checks}
for row in index:
    source = by_id[row["source_id"]]
    assert source["name_candidate"] == row["target"]
    assert source["signature_sha256"] == row["signature_sha256"]
    check = by_file[row["module"]]
    assert check["exit"] == 0 and check["outcome"] == "exit"
    assert check["minimum_available"] >= check["reserve"] >= 4*1024**3
    assert check["swap_total"] == 0
    assert hashlib.sha256((root / row["module"]).read_bytes()).hexdigest() == check["sha256"]
    assert any(t.name == "lean" for t in map(Path, check["command"]))
    assert "-j1" in check["command"] and "--tstack=131072" in check["command"]
    log = Path(check["log"]).read_text()
    accepted = [f"'{row['witness']}' does not depend on any axioms",
                f"'{row['witness']}' depends on axioms: [propext]"]
    assert any(line in log.splitlines() for line in accepted), row["witness"]
    marker = f"H62_WITNESS {row['witness']} FOR {row['target']}"
    assert marker in log.splitlines(), marker
    assert "sorryAx" not in log
    # Authenticate the target's actual importing source too. H82 permits only
    # the exact received proof postimage when bytes differ from the frozen file.
    target_import = by_file[source["path"]]
    assert target_import["exit"] == 0 and target_import["outcome"] == "exit"
    actual_source = (root / source["path"]).read_bytes()
    assert hashlib.sha256(actual_source).hexdigest() == target_import["sha256"]
    if target_import["sha256"] != census["sources"][source["path"]]["sha256"]:
        from overlay_review import TRUSTED, reconstruct, fidelity, receipt_patch_path
        from census import git
        receipts = json.loads((root / "tests/h62/item2/audit-language/received-overlays.json").read_text())
        candidates = [r for r in receipts if TRUSTED[r["label"]]["path"] == source["path"]]
        assert len(candidates) == 1
        receipt = candidates[0]
        trusted = TRUSTED[receipt["label"]]
        patch = receipt_patch_path(receipt).read_bytes()
        assert hashlib.sha256(patch).hexdigest() == trusted["sha256"]
        frozen_source = git("show", f"{census['base']}:{source['path']}")
        assert hashlib.sha256(frozen_source).hexdigest() == census["sources"][source["path"]]["sha256"]
        approved, *_ = reconstruct(patch, frozen_source, source["path"])
        fidelity(source["path"], frozen_source, approved)
        assert actual_source == revisions.get(source["path"], approved)
    # Each independent frozen import remains byte-for-byte tied to the census hash.
    for path in ("Solidity/Language/Features.lean", "Solidity/Language/FeatureInfo.lean",
                 "Solidity/KeySort.lean", "Solidity/Syntax/CheckedExact.lean"):
        original = by_file[path]
        assert original["exit"] == 0
        assert original["sha256"] == census["sources"][path]["sha256"]
covered = {r["source_id"] for r in index}
report = {"status": "partial", "base": census["base"], "source_declarations": len(by_id),
          "checked_full_telescope_certificates": len(covered),
          "uncovered_source_declarations": len(by_id)-len(covered),
          "interface_classification": "pending; conservative source superset",
          "compiler_totality": "pending; ABI decoder controls do not cover compilers",
          "verified": index, "uncovered": [d for d in census["declarations"] if d["id"] not in covered]}
args.output.mkdir(parents=True, exist_ok=True)
payload = (json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True)+"\n").encode()
(args.output / "statement-fidelity.json").write_bytes(payload)
(args.output / "statement-fidelity.sha256").write_text(hashlib.sha256(payload).hexdigest()+"  statement-fidelity.json\n")
print(json.dumps({k:v for k,v in report.items() if k not in ("verified", "uncovered")}, sort_keys=True))
