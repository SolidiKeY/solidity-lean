#!/usr/bin/env python3
"""Actual launcher negative controls; these IO fixtures are not proof oracles."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import sys
import bounded


def expected_outcome(label, result, text):
    if label == "allowed-import":
        return result["kind"] == "exit" and result["exit"] == 0
    if label == "forbidden-downstream-import":
        return result["kind"] == "exit" and result["exit"] == 1 and "Taclet.olean' of module Solidity.Calculus.Taclet does not exist" in text
    if label == "readonly-source":
        return result["kind"] == "exit" and result["exit"] == 1 and "read-only file system" in text.lower() and result["source_unchanged"]
    if label == "timeout":
        return result["kind"] == "timeout" and result["exit"] is None
    raise ValueError("unknown backend control")


def control_summary(records, labels):
    done = {r["label"] for r in records}
    return {"boundary": "External launcher controls only", "checks": records,
            "unrun": [label for label in labels if label not in done],
            "pass": len(records) == len(labels) and done == set(labels) and all(r["passed"] for r in records)}


def run(repo, output):
    output.mkdir(exist_ok=False)
    cache = Path("/workspace/h28-runtime/prepared-base-6f3eedf0/.lake/build/lib/lean")
    cases = [
        ("allowed-import", "import Solidity.Calculus.PremiseSound\nexample : True := by trivial\n", 20),
        ("forbidden-downstream-import", "import Solidity.Calculus.Taclet\n", 20),
        ("readonly-source", '#eval IO.FS.writeFile "Solidity/Calculus/Rules.lean" "corrupt"\n', 20),
        ("timeout", "#eval IO.sleep 5000\n", 2)]
    records = []
    for label, source, timeout in cases:
        with tempfile.TemporaryDirectory(prefix="h28-backend-control-", dir="/workspace/h28-runtime") as scratch:
            tree = Path(scratch)
            (tree / "Probe.lean").write_text(source)
            sentinel = tree / "Solidity/Calculus/Rules.lean"
            sentinel.parent.mkdir(parents=True)
            sentinel.write_bytes((repo / "Solidity/Calculus/Rules.lean").read_bytes())
            before = hashlib.sha256(sentinel.read_bytes()).hexdigest()
            for path in cache.rglob("*.olean"):
                if path.name in ("Rules.olean", "Taclet.olean", "CallbackRules.olean", "RuleKit.olean"):
                    continue
                dest = tree / ".lake/build/lib/lean" / path.relative_to(cache)
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.symlink_to(Path("/cache") / path.relative_to(cache))
            result = bounded.lean(tree, "Probe.lean", output / (label + ".log"), timeout=timeout, cache=cache)
            text = (output / (label + ".log")).read_text()
            result.update(label=label, fixture=source, source_unchanged=before == hashlib.sha256(sentinel.read_bytes()).hexdigest())
            passed = expected_outcome(label, result, text)
            search = next(arg for arg in result["argv"] if arg.startswith("LEAN_PATH="))
            passed = passed and search == "LEAN_PATH=/task/.lake/build/lib/lean"
            name = result["argv"][result["argv"].index("--name") + 1]
            still_present = subprocess.run(bounded.DOCKER + ["inspect", name], env=bounded.docker_env(), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
            result.update(passed=passed and not still_present, container_cleaned=not still_present)
            records.append(result)
            (output / "result.json").write_text(json.dumps(control_summary(records, [item[0] for item in cases]), indent=2) + "\n")
            print(label, result["kind"], result["exit"], result["passed"], flush=True)
            if not result["passed"]: raise RuntimeError("backend control failed: " + label)


if __name__ == "__main__":
    repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    run(repo, Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else repo / "tests/h28-sol/mutation-testing/evidence/backend-controls-final")
