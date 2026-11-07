#!/usr/bin/env python3
"""Run current H55 controls against their exact frozen Git source snapshot.

This is frozen-input validation, not live Raw coverage or Lean acceptance.
Production files are read only; the disposable snapshot is always removed.
"""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[3]
BASE = "4d3790eadb8a5212233bc7d5e345817476b2f590"
AREAS = ("scripts/h55/vectors-tables", "tests/h55/vectors-tables")


def environment():
    result = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    result["PYTHONDONTWRITEBYTECODE"] = "1"
    return result


def git(*args):
    return subprocess.check_output(
        ["git", "-c", "safe.directory=" + str(ROOT), "-C", str(ROOT), *args],
        env=environment())


def run():
    tooling = {}
    for area in AREAS:
        component = ROOT
        for part in Path(area).parts:
            component = component / part
            if component.is_symlink():
                raise ValueError("symlinked tooling directory: " + str(component))
        for path in sorted((ROOT / area).rglob("*")):
            if path.is_symlink():
                raise ValueError("symlinked tooling input: " + str(path))
            if path.is_file() and "__pycache__" not in path.parts:
                tooling[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    archive = git("archive", BASE, "Solidity")
    with tempfile.TemporaryDirectory(prefix="h55-frozen-", dir="/workspace/scratch") as name:
        snapshot = Path(name)
        with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as source:
            source.extractall(snapshot, filter="data")
        for area in AREAS:
            shutil.copytree(ROOT / area, snapshot / area,
                            ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        command = [sys.executable, "-B", "-m", "unittest", "discover",
                   "-s", "tests/h55/vectors-tables", "-p", "test_*.py", "-v"]
        result = subprocess.run(command, cwd=snapshot, env=environment(),
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        sys.stderr.write(result.stdout)
    return {
        "schema_version": 1,
        "validation": "frozen-source Python controls",
        "base": BASE,
        "source_archive_sha256": hashlib.sha256(archive).hexdigest(),
        "tooling_head": git("rev-parse", "HEAD").decode().strip(),
        "tooling_files_sha256": tooling,
        "exit_code": result.returncode,
        "snapshot_removed": not snapshot.exists(),
        "limitations": "Not live-tree semantic coverage, Lean validation, or migration acceptance."
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, help="new off-repository JSON report path")
    args = parser.parse_args()
    if args.report:
        report = args.report.resolve()
        if report.is_relative_to(ROOT) or report.exists():
            parser.error("report must be a new off-repository path")
    data = run()
    text = json.dumps(data, sort_keys=True, indent=2) + "\n"
    if args.report:
        with args.report.open("x") as output:
            output.write(text)
    sys.stdout.write(text)
    return data["exit_code"]


if __name__ == "__main__":
    raise SystemExit(main())
