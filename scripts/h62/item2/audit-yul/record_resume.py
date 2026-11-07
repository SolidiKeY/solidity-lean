#!/usr/bin/env python3
"""Accept this resumed milestone's exact source-bound proof gates only."""
import argparse
import hashlib
import json
import pathlib
import subprocess
import fcntl
import resume_inventory

PREFIX = "Solidity.Yul.Compilation."
JOINT = {
    "Slots.bounds": "bounds_joint", "Slots.injective": "injective_joint",
    "Slots.extend_at": "extend_joint", "Slots.relocate": "relocate_joint",
    "Frame.local_bound": "local_bound_joint", "Frame.caller_below_locals": "caller_joint",
    "returnHeight_compose": "height_joint", "label_injective": "label_injective_joint",
    "label_relocate": "label_relocate_joint"}
SEPARATIONS = {
    "Frame.arg_result_disjoint": "Argument/result allocated intervals are disjoint.",
    "Frame.result_local_disjoint": "Result/local allocated intervals are disjoint.",
    "Frame.arg_local_disjoint": "Argument/local allocated intervals are disjoint."}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_gate(evidence, module):
    rows = [json.loads(line) for line in (evidence / "commands.jsonl").read_text().splitlines()]
    if not rows or any(row["exit"] or row["stop_reason"] for row in rows):
        raise ValueError("proof gate failed or stopped")
    for row in rows:
        source = pathlib.Path(row["command"][-1])
        if sha(source) != row["source_sha256"]:
            raise ValueError("stale proof/import source: " + str(source))
    matches = [row for row in rows if row["command"][-1] == module]
    if len(matches) != 1:
        raise ValueError("proof gate must have exactly one current helper compilation")
    log = pathlib.Path(matches[0]["log"]).read_text()
    return rows, log


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--evidence", type=pathlib.Path, required=True)
    ap.add_argument("--original-census", type=pathlib.Path, required=True)
    ap.add_argument("--output", type=pathlib.Path, required=True)
    ap.add_argument("--base", default="5da4771e63a4278ed53932ac39a032e3d7aea6ed")
    args = ap.parse_args()
    with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock", "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if sha(args.original_census) != resume_inventory.ORIGINAL_CENSUS_SHA256:
            raise ValueError("original census identity mismatch")
        original = json.loads(args.original_census.read_text())
        inventory_path = args.evidence / "inventory/inventory.json"
        inventory = json.loads(inventory_path.read_text())
        expected_inventory = resume_inventory.reconcile(args.original_census, args.base)
        if inventory != expected_inventory:
            raise ValueError("inventory baseline/source snapshot mismatch")
        allocation = pathlib.Path("Solidity/Yul/Compilation/Allocation.lean")
        reserved = pathlib.Path("Solidity/Yul/ReservedNames.lean")
        frozen = lambda p: subprocess.check_output(["git", "show", original["base"] + ":" + str(p)])
        if frozen(allocation) != allocation.read_bytes():
            raise ValueError("original Allocation interface changed")
        old_reserved = frozen(reserved)
        old_count = b"theorem reservedNames_count : reservedNames.length = 157 := rfl"
        new_count = b"theorem reservedNames_count : reservedNames.length = 157 := by decide +kernel"
        if old_reserved.count(old_count) != 1 or old_reserved.replace(old_count, new_count) != reserved.read_bytes():
            raise ValueError("reservation statement or dependency changed beyond known count proof")
        am = "tests/h62/item2/audit-yul/AllocationWitnesses.lean"
        rm = "tests/h62/item2/audit-yul/ReservedRefutation.lean"
        allocation_gates, alog = checked_gate(args.evidence / "allocation-final", am)
        reserved_gates, rlog = checked_gate(args.evidence / "reserved-refutation", rm)
        baseline_tree = resume_inventory.tree(expected_inventory["current_base"])
        for gate in allocation_gates + reserved_gates:
            source = gate["command"][-1]
            if source.startswith("tests/h62/item2/audit-yul/"):
                continue
            oid = subprocess.check_output(["git", "hash-object", source]).decode().strip()
            if baseline_tree.get(source) != oid:
                raise ValueError("compiled import differs from declared baseline: " + source)
        rows = []; sources = original["declarations"]
        def record(name, proof, module, status, reason, marker, log):
            matches = [r for r in sources if r["kind"] == "theorem" and r["source_name"] == name]
            if len(matches) != 1 or matches[0]["witness_status"] != "uncovered":
                raise ValueError("not one previously uncovered original theorem: " + name)
            if log.count(marker) != 1:
                raise ValueError("missing/duplicate successful fidelity record: " + name)
            row = matches[0]
            rows.append(dict(theorem=name, original_id=row["id"], owner=row["owner"],
                frozen_signature=row["signature"], frozen_signature_sha256=row["signature_sha256"],
                proof=proof, proof_module=module, proof_source_sha256=sha(pathlib.Path(module)),
                status=status, audit_criterion="H69" if status == "intentional_refutation_proved" else "complete reducing existential telescope",
                reason=reason))
        for suffix, proof in JOINT.items():
            record(PREFIX + suffix, "H62.AuditYul.AllocationWitnesses." + proof, am,
                "joint_witness_proved", "All exposed arguments and coupled premises supplied simultaneously; independent reducing type check.",
                "ALLOCATION_JOINT_PASS: " + PREFIX + suffix, alog)
        for suffix, reason in SEPARATIONS.items():
            record(PREFIX + suffix, "H62.AuditYul.AllocationWitnesses." + suffix.split(".")[-1], am,
                "intentional_refutation_proved", reason + " Assuming overlap is intentionally contradictory; full original type retained.",
                "ALLOCATION_REFUTATION_PASS: " + PREFIX + suffix, alog)
        record("Solidity.Yul.slotnum_not_reserved", "H62.AuditYul.ReservedRefutation.slotnum_not_reserved", rm,
            "intentional_refutation_proved", "SLOTNUM is absent from the pinned reservation list; membership is intentionally refuted. No executable-builtin/runtime claim.",
            "RESERVED_REFUTATION_FIDELITY_PASS: unchanged full type and universes", rlog)
        expected = {r["source_name"] for r in sources if r["file"] == str(allocation) and r["kind"] == "theorem"}
        if expected != {r["theorem"] for r in rows if r["proof_module"] == am}:
            raise ValueError("Allocation declaration census incomplete")
        result = dict(original_base=original["base"], baseline=expected_inventory["current_base"],
            inventory_sha256=sha(inventory_path), inventory_generator_sha256=sha(pathlib.Path(resume_inventory.__file__)),
            original_census_sha256=sha(args.original_census), original_named_theorems=19230,
            new_joint_witnesses=9, new_intentional_refutations=4,
            original_baseline_combined_accounting=dict(joint_witnesses=14, intentional_refutations=15,
                without_exposed_hypotheses=513, uncovered_named_theorems=18688, pending_negative_classifications=46),
            fresh_current_baseline_accounting=dict(joint_witnesses=9, intentional_refutations=4,
                historical_results_not_promoted=True),
            statements=rows, proof_commands=allocation_gates + reserved_gates,
            original_interfaces_changed=False, runtime_gate_pass=False,
            boundary="Arithmetic/reservation interfaces only; all original wider queue and final gates remain open.")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        print("RESUME_REGISTRY_PASS: 9 ordinary joint witnesses; 4 intentional refutations; all 12 Allocation declarations accounted exactly once")


if __name__ == "__main__":
    main()
