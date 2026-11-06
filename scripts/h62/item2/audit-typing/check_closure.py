#!/usr/bin/env python3
"""Serial, bounded isolated-output reproduction of the Closure audit only."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
EVIDENCE = Path("/workspace/h62-audit-typing-evidence")
LEAN = Path("/workspace/h62-audit-typing-tools/lean-4.35.0-linux/bin/lean")
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
TESTS = "tests/h62/item2/audit-typing/"

def main():
    EVIDENCE.mkdir(exist_ok=True)
    lockpath = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    lockpath.parent.mkdir(exist_ok=True)
    with lockpath.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        source = "Solidity/Frontend/Static/Closure.lean"
        frozen = subprocess.check_output(["git", "show", f"{BASE}:{source}"], cwd=ROOT)
        assert (ROOT/source).read_bytes() == frozen, "Frozen interface changed"
        archive = EVIDENCE/"lean-4.35.0-linux.tar.zst"
        with archive.open("rb") as stream:
            assert hashlib.file_digest(stream, "sha256").hexdigest() == "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d"
        env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(EVIDENCE/"olean"))
        results = []
        for path in [source, TESTS+"DeclarationCensus.lean", TESTS+"ClosureWitnesses.lean", TESTS+"ClosureCensus.lean", TESTS+"ClosureFidelity.lean"]:
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
        assert len(census) == len({r["name"] for r in census}) == 33
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
        print("Closure-only audit checks passed; full assignment pending")

if __name__ == "__main__":
    main()
