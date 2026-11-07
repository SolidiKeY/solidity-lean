#!/usr/bin/env python3
"""Serial, bounded isolated-output reproduction of the Closure and Values-list audit subsets."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import re
import subprocess
import time
import sys

# Keep generated Python bytecode out of the owned source tree.
sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[4]
EVIDENCE = Path("/workspace/h62-audit-typing-evidence/v4.24.0")
LEAN = Path("/workspace/.setup/tools/lean-4.24.0-linux/bin/lean")
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
TESTS = "tests/h62/item2/audit-typing/"

def main():
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    lockpath = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    lockpath.parent.mkdir(exist_ok=True)
    with lockpath.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        source = "Solidity/Frontend/Static/Closure.lean"
        frozen = subprocess.check_output(["git", "show", f"{BASE}:{source}"], cwd=ROOT)
        assert (ROOT/source).read_bytes() == frozen, "Frozen interface changed"
        assert (ROOT/"lean-toolchain").read_text().strip() == "leanprover/lean4:v4.24.0"
        versions = subprocess.check_output([str(LEAN), "--version"], text=True)
        assert "version 4.24.0," in versions
        lake_version = subprocess.check_output([str(LEAN.with_name("lake")), "--version"], text=True)
        (EVIDENCE/"versions.txt").write_text(versions+lake_version)
        prerequisites = json.loads((EVIDENCE/"typing-values-build-results.json").read_text())
        plan = json.loads((EVIDENCE/"typing-values-build-plan.json").read_text())
        assert [r["command"][-1] for r in prerequisites] == plan
        assert plan[-1] == "Solidity/Typing/Values.lean"
        for record in prerequisites:
            assert record["exit"] == 0 and record["stopped"] is None
            path = record["command"][-1]
            assert record["command"][0] == str(LEAN)
            frozen_dependency = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT)
            assert (ROOT/path).read_bytes() == frozen_dependency
            assert hashlib.sha256(frozen_dependency).hexdigest() == record["source_sha256"]
            artifact = EVIDENCE/"olean"/Path(path).with_suffix(".olean")
            assert hashlib.sha256(artifact.read_bytes()).hexdigest() == record["olean_sha256"]
        frontend_records = json.loads((EVIDENCE/"frontend-units-build-results.json").read_text())
        frontend_plan = json.loads((EVIDENCE/"frontend-units-build-plan.json").read_text())
        assert [r["command"][-1] for r in frontend_records] == frontend_plan
        assert frontend_plan[-1] == "Solidity/Frontend/Static/UnitsExamples.lean"
        for record in frontend_records:
            assert record["exit"] == 0 and record["stopped"] is None
            assert record["command"][0] == str(LEAN)
            path = record["command"][-1]
            frozen_dependency = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT)
            assert (ROOT/path).read_bytes() == frozen_dependency
            assert hashlib.sha256(frozen_dependency).hexdigest() == record["source_sha256"]
            artifact = EVIDENCE/"olean"/Path(path).with_suffix(".olean")
            assert hashlib.sha256(artifact.read_bytes()).hexdigest() == record["olean_sha256"]
        env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(EVIDENCE/"olean"))
        results = []
        for path in [source, TESTS+"DeclarationCensus.lean", TESTS+"ClosureWitnesses.lean", TESTS+"ClosureCensus.lean", TESTS+"ClosureFidelity.lean", TESTS+"ValuesListsWitnesses.lean", TESTS+"ValuesListsFidelity.lean", TESTS+"ValuesDefaultsWitnesses.lean", TESTS+"ValuesDefaultsFidelity.lean", TESTS+"UnitsSuccess.lean", TESTS+"UnitsSuccessFidelity.lean", TESTS+"ValuesHeredWitnesses.lean", TESTS+"ValuesHeredFidelity.lean", TESTS+"ValuesOpsWitnesses.lean", TESTS+"ValuesOpsFidelity.lean", TESTS+"ProvisionedCensus.lean"]:
            current = int(Path("/sys/fs/cgroup/memory.current").read_text())
            cap = int(Path("/sys/fs/cgroup/memory.max").read_text())
            assert cap-current >= 4*1024**3, "Insufficient 4 GiB reserve"
            output = EVIDENCE/"olean"/Path(path).with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            command = [str(LEAN), "-j1", "--memory=11000", "--tstack=131072", "-o", str(output), path]
            start = time.monotonic()
            log = EVIDENCE/(Path(path).stem+"-checked.log")
            stopped = None
            with log.open("w") as stream:
                process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
                while process.poll() is None:
                    current = int(Path("/sys/fs/cgroup/memory.current").read_text())
                    if cap-current < 4*1024**3:
                        stopped = "4 GiB reserve guard"
                    if time.monotonic()-start > 120:
                        stopped = "120 second timeout"
                    if stopped:
                        process.terminate()
                        try:
                            process.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            process.kill()
                            process.wait()
                        break
                    time.sleep(0.1)
            result = dict(command=command, exit=process.returncode, seconds=time.monotonic()-start,
                log=str(log), stopped=stopped, cumulative_child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
            results.append(result)
            (EVIDENCE/"closure-check-results.json").write_text(json.dumps(results, indent=2)+"\n")
            print(path, process.returncode, flush=True)
            if stopped or process.returncode:
                raise SystemExit(process.returncode or 1)
        fidelity = (EVIDENCE/"ClosureFidelity-checked.log").read_text()
        checked = re.findall(r"^AUDIT-WITNESS (\S+) via", fidelity, re.M)
        expected = ["Solidity.Frontend.Static."+name for name in
            re.findall(r"^theorem (\S+)", frozen.decode(), re.M)]
        assert len(checked) == len(set(checked)) == 23
        assert set(checked) == set(expected), "Source theorem reconciliation failed"
        assert "sorryAx" not in fidelity
        census = [json.loads(line.split("AUDIT-DECL ", 1)[1]) for line in
            (EVIDENCE/"ClosureCensus-checked.log").read_text().splitlines() if "AUDIT-DECL " in line]
        assert len(census) == len({r["name"] for r in census}) == 32
        assert set(expected) <= {r["name"] for r in census}
        mappings = dict(re.findall(r"^AUDIT-WITNESS (\S+) via (\S+):", fidelity, re.M))
        for row in census:
            source_interface = row["name"] in set(expected)
            row["classification"] = "source-interface" if source_interface else "generated-pending-interface-status"
            row["witness"] = mappings.get(row["name"])
            row["owner"] = None
            row["owner_status"] = "live-producer-identity-pending-coordinator"
            row["global_premises"] = "Bool carrier and actual DecidableEq Bool; Reach.trans/Closed.reach omit unused instance" if source_interface else None
        (EVIDENCE/"closure-coverage.json").write_text(json.dumps(census, sort_keys=True, indent=2)+"\n")
        values_log = (EVIDENCE/"ValuesListsFidelity-checked.log").read_text()
        values_checked = re.findall(r"^AUDIT-WITNESS (\S+) via", values_log, re.M)
        expected_values = ["Solidity."+name for name in ["lookupBy_isSome_of_mem'", "lookupBy_of_nodup",
            "mem_setBy", "lookupBy_none_setBy", "nodupKeysB_setBy'", "setBy_of_lookupBy",
            "lookupBy_append_none", "setBy_append_none", "nodupKeysB_mid"]]
        assert len(values_checked) == len(set(values_checked)) == 9
        assert set(values_checked) == set(expected_values)
        assert "sorryAx" not in values_log
        values_census = [json.loads(line.split("AUDIT-DECL ", 1)[1]) for line in
            values_log.splitlines() if "AUDIT-DECL " in line]
        assert len(values_census) == len({r["name"] for r in values_census})
        assert set(expected_values) <= {r["name"] for r in values_census}
        (EVIDENCE/"values-census.json").write_text(json.dumps(values_census, sort_keys=True, indent=2)+"\n")
        defaults_log = (EVIDENCE/"ValuesDefaultsFidelity-checked.log").read_text()
        default_checked = re.findall(r"^AUDIT-FULL-INPUTS (\S+) via", defaults_log, re.M)
        expected_defaults = {"Solidity."+n for n in ["SVal.dfltBelow_irrel", "SVal.dfltBelow_dflt",
            "SFields.dfltBelow_eq", "SVal.dflt_all", "SFields.dflt_all", "SVal.dfltBelow_all"]}
        assert len(default_checked) == len(set(default_checked)) == 6
        assert set(default_checked) == expected_defaults
        assert "sorryAx" not in defaults_log
        units_log = (EVIDENCE/"UnitsSuccessFidelity-checked.log").read_text()
        assert units_log.count("AUDIT-FULL-INPUTS Solidity.Frontend.Static.unitsChecker_complete via ") == 1
        assert "sorryAx" not in units_log
        hered_log = (EVIDENCE/"ValuesHeredFidelity-checked.log").read_text()
        hered_checked = re.findall(r"^AUDIT-FULL-INPUTS (\S+) via", hered_log, re.M)
        expected_hered = {"Solidity."+kind+"."+suffix for kind in ["SVal", "SFields", "SList", "SVec", "SMap"] for suffix in ["all_mono", "allB_iff"]}
        assert len(hered_checked) == len(set(hered_checked)) == 10
        assert set(hered_checked) == expected_hered
        assert "sorryAx" not in hered_log
        ops_log = (EVIDENCE/"ValuesOpsFidelity-checked.log").read_text()
        ops_checked = re.findall(r"^AUDIT-FULL-INPUTS (\S+) via", ops_log, re.M)
        expected_ops = {"Solidity."+n for n in ['SVal.strip_all', 'SFields.strip_all', 'SVec.strip_all', 'SVal.defaultOf_all', 'SFields.defaultOf_all', 'SVec.defaultOf_all', 'SVal.overlay_all', 'SFields.overlay_all', 'SVec.overlayOn_all']}
        assert len(ops_checked) == len(set(ops_checked)) == 9
        assert set(ops_checked) == expected_ops
        assert "sorryAx" not in ops_log
        module_inventory = json.loads((EVIDENCE/"provisioned-module-inventory.json").read_text())
        assert module_inventory["base"] == BASE
        provisioned = {r["module"]: r for r in module_inventory["selected"]}
        whole_log = (EVIDENCE/"ProvisionedCensus-checked.log").read_text()
        all_rows = [json.loads(line.split("AUDIT-DECL ", 1)[1]) for line in whole_log.splitlines() if "AUDIT-DECL " in line]
        assert len(all_rows) == len({r["name"] for r in all_rows})
        assert {r["module"] for r in all_rows} <= set(provisioned)
        module_markers = re.findall(r"^AUDIT-MODULE (\S+) theorem-count=(\d+)", whole_log, re.M)
        assert len(module_markers) == len({m for m, _ in module_markers}) == len(provisioned)
        assert {m for m, _ in module_markers} == set(provisioned)
        module_counts = {m: int(count) for m, count in module_markers}
        for module, count in module_counts.items():
            assert count == sum(row["module"] == module for row in all_rows)
        witnesses = {}
        for log_name in ["ClosureFidelity", "ValuesListsFidelity", "ValuesDefaultsFidelity", "UnitsSuccessFidelity", "ValuesHeredFidelity", "ValuesOpsFidelity"]:
            content = (EVIDENCE/(log_name+"-checked.log")).read_text()
            for name, witness in re.findall(r"^AUDIT-(?:WITNESS|FULL-INPUTS) (\S+) via (\S+):", content, re.M):
                assert name not in witnesses
                witnesses[name] = witness
        assert len(witnesses) == 58
        assert set(witnesses) <= {r["name"] for r in all_rows}
        for row in all_rows:
            provenance = provisioned[row["module"]]
            row["source_path"] = provenance["path"]
            row["frozen_source_sha256"] = provenance["frozen_source_sha256"]
            row["owner"] = None
            row["owner_status"] = "live-producer-identity-unconfirmed"
            row["historical_last_change"] = provenance["historical_last_change"]
            row["witness"] = witnesses.get(row["name"])
            row["status"] = "witness-checked" if row["witness"] else "uncovered-interface-classification-and-witness-pending"
            row["hypothesis_roles"] = "reviewed-in-hypothesis-roles.json" if row["witness"] else "pending"
        all_rows.sort(key=lambda row: row["name"])
        result = dict(base=BASE, modules=len(provisioned), module_counts=module_counts, declarations=all_rows,
            witnessed=len(witnesses), unprovisioned_modules=module_inventory["unprovisioned"],
            limitations=module_inventory["limitations"])
        (EVIDENCE/"statement-census.json").write_text(json.dumps(result, sort_keys=True, indent=2)+"\n")
        uncovered = [r for r in all_rows if not r["witness"]]
        (EVIDENCE/"uncovered-statements.tsv").write_text("name\tmodule\towner_status\n"+"".join(
            r["name"]+"\t"+r["module"]+"\tlive-producer-identity-unconfirmed\n" for r in uncovered))
        from classify_roles import classify
        classify()
        print(f"{len(all_rows)} exact theorem constants in {len(provisioned)} modules; 58 witnessed; {len(uncovered)} pending; full assignment pending")

if __name__ == "__main__":
    main()
