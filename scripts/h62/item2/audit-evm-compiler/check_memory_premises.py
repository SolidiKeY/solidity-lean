#!/usr/bin/env python3
"""Check the audit with repository Lake settings and fresh test-helper oleans.
Run through `lake env`; the caller holds the repository writer lock. Core
imports must already be built and materialized on Lake's LEAN_PATH. No alternate
lakefile, generated-root registration or prebuilt audit helper is required.
"""
import argparse
import hashlib
import json
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[4]
PREFIX = pathlib.Path("tests/h62/item2/audit-evm-compiler")
MODULES = ["JointImpossible", "JointWitness", "MemoryPremiseAudit"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", required=True, type=pathlib.Path)
    args = parser.parse_args()
    if pathlib.Path.cwd().resolve() != ROOT:
        parser.error("run from the repository root")
    lake_path = str(ROOT / ".lake/build/lib/lean")
    inherited = os.environ.get("LEAN_PATH", "")
    if lake_path not in inherited.split(os.pathsep):
        parser.error("launch with the repository's `lake env python3`")
    evidence = args.evidence.resolve()
    if evidence.is_relative_to(ROOT):
        parser.error("evidence must be outside the repository")
    if evidence.exists() and any(evidence.iterdir()):
        parser.error("evidence directory must be new or empty; existing output preserved")
    evidence.mkdir(parents=True, exist_ok=True)
    scratch = pathlib.Path(tempfile.mkdtemp(prefix="fresh-audit-", dir=evidence))
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    env["LEAN_PATH"] = str(scratch) + os.pathsep + inherited
    versions = []
    for command in [["lean", "--version"], ["lake", "--version"]]:
        result = subprocess.run(command, check=True, capture_output=True, text=True, env=env)
        versions.append(dict(command=command, exit=0, output=result.stdout.strip()))
    (evidence / "versions.json").write_text(json.dumps(versions, indent=2) + "\n")
    commands = [("keysort", ["lean", "-j1", "--tstack=131072", "Solidity/KeySort.lean"])]
    for module in MODULES:
        source = PREFIX / (module + ".lean")
        output = scratch / source.with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        commands.append((module, ["lean", "-j1", "--tstack=131072", "-o", str(output), str(source)]))
    receipts = []
    for name, command in commands:
        runner = [sys.executable, str(pathlib.Path(__file__).with_name("bounded.py")),
                  "--seconds", "300", "--output", str(evidence / name), "--"] + command
        result = subprocess.run(runner, env=env)
        receipts.append(dict(command=command, exit=result.returncode, receipt=name + ".json"))
        if result.returncode:
            return result.returncode
    source_paths = [pathlib.Path("lakefile.toml"), pathlib.Path("lean-toolchain"),
                    pathlib.Path(__file__).relative_to(ROOT),
                    pathlib.Path(__file__).with_name("bounded.py").relative_to(ROOT)]
    source_paths += [PREFIX / (module + ".lean") for module in MODULES]
    summary = dict(status="pass", repository=str(ROOT), lakefile="lakefile.toml",
                   core_lean_path=inherited, fresh_audit_library=str(scratch),
                   gates=receipts, versions=versions,
                   sources=[dict(path=str(p), sha256=hashlib.sha256((ROOT / p).read_bytes()).hexdigest())
                            for p in source_paths],
                   scope="Fresh audit helper compilation and five joint premise witnesses; not full library validation")
    (evidence / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print("PASS: repository Lake environment; fresh JointImpossible/JointWitness; five memory joint witnesses")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
