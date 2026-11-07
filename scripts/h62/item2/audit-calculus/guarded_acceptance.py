#!/usr/bin/env python3
"""Regression guard: truncated census, self-certified toolchains and lost aggregates.

Expected runtime fingerprints are explicit caller inputs, not approvals granted
by this tool. Preflight is not proof acceptance. Underlying acceptance runs in a
fresh external evidence view; original evidence and aggregates are never edited.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
from classify_frozen_signatures import authenticated_census, EXPECTED_CENSUS

REPO = Path(__file__).resolve().parents[4]


def digest(path):
    hasher = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            hasher.update(block)
    return hasher.hexdigest()


def runtime_binding(records, toolchain, expected_lean, import_manifest, expected_imports):
    toolchain = toolchain.resolve()
    if digest(toolchain / "bin/lean") != expected_lean:
        raise ValueError("Lean executable differs from explicit expected fingerprint")
    manifest_bytes = import_manifest.read_bytes()
    if hashlib.sha256(manifest_bytes).hexdigest() != expected_imports:
        raise ValueError("import manifest differs from explicit expected fingerprint")
    if not records:
        raise ValueError("missing compile/export receipts")
    for row in records:
        if row.get("schema") != 2 or row.get("lean_sha256") != expected_lean:
            raise ValueError("unbound or mixed toolchain receipt")
    entries = json.loads(manifest_bytes)
    count = 0
    for key, expected in entries.items():
        if not key.startswith("@toolchain/"):
            continue
        relative = key.removeprefix("@toolchain/")
        path = PurePosixPath(relative)
        target = toolchain / relative
        if path.is_absolute() or ".." in path.parts or str(path) != relative or not target.resolve().is_relative_to(toolchain):
            raise ValueError("invalid toolchain import path")
        if digest(target) != expected:
            raise ValueError("toolchain import differs from expected manifest: " + relative)
        count += 1
    if not count:
        raise ValueError("missing toolchain import fingerprints")
    return count


def publish_json(target, value):
    """Atomically publish a fresh result; never replace an existing aggregate."""
    target = target.parent.resolve() / target.name
    if target.is_relative_to(REPO):
        raise ValueError("H44: result must be external")
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write((json.dumps(value, indent=2) + "\n").encode())
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, target)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def stage_baseline(directory, baseline, ledger_bytes):
    """Freeze the validated ledger; retain hash-checked artifact paths."""
    directory.mkdir(exist_ok=False)
    (directory / "lean-commands.jsonl").write_bytes(ledger_bytes)
    for path in baseline.resolve().iterdir():
        if path.name != "lean-commands.jsonl":
            (directory / path.name).symlink_to(path.resolve(), target_is_directory=path.is_dir())


def complete_exit(legacy_exit, historical_imports_bound):
    return legacy_exit if legacy_exit else (0 if historical_imports_bound else 89)


def evidence_view(directory, census_path, baseline, ledger_bytes=None):
    """Build a fresh view so the legacy gate cannot unlink a prior aggregate."""
    census_bytes = census_path.read_bytes()
    if hashlib.sha256(census_bytes).hexdigest() != EXPECTED_CENSUS:
        raise ValueError("incomplete or changed frozen census")
    directory.mkdir(exist_ok=False)
    (directory / "source-census.json").write_bytes(census_bytes)
    if ledger_bytes is None:
        ledger_bytes = (baseline / "lean-commands.jsonl").read_bytes()
    stage_baseline(directory / "baseline", baseline, ledger_bytes)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--census", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--expected-lean-sha256", required=True)
    parser.add_argument("--import-manifest", type=Path, required=True)
    parser.add_argument("--expected-import-manifest-sha256", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--preflight-only", action="store_true")
    args = parser.parse_args()
    output = args.out.resolve()
    if output.is_relative_to(REPO) or output.is_relative_to(args.root.resolve()):
        parser.error("H44: output must be outside both repositories")
    source = authenticated_census(args.census)
    ledger_bytes = (args.baseline / "lean-commands.jsonl").read_bytes()
    records = [json.loads(line) for line in ledger_bytes.decode().splitlines()]
    imports = runtime_binding(records, args.toolchain, args.expected_lean_sha256,
                              args.import_manifest, args.expected_import_manifest_sha256)
    output.mkdir(parents=True, exist_ok=False)
    historical_bound = all(row.get("toolchain_manifest_sha256") == args.expected_import_manifest_sha256 for row in records)
    summary = {"boundary": "Current runtime/census preflight only; no proof, trust approval or migration acceptance",
               "receipt_ledger_sha256": hashlib.sha256(ledger_bytes).hexdigest(),
               "historical_import_binding": "recorded" if historical_bound else "UNVERIFIABLE: receipt-level import manifest binding missing",
               "source_candidates": len(source["declarations"]), "receipt_count": len(records),
               "failed_receipts": sum(row.get("exit") != 0 for row in records),
               "toolchain_imports_checked": imports, "expected_lean_sha256": args.expected_lean_sha256,
               "expected_import_manifest_sha256": args.expected_import_manifest_sha256,
               "preflight_only": args.preflight_only}
    publish_json(output / "preflight.json", summary)
    if args.preflight_only:
        print(json.dumps(summary, sort_keys=True))
        return
    view = output / "evidence-view"
    evidence_view(view, args.census, args.baseline, ledger_bytes)
    command = [sys.executable, str(Path(__file__).with_name("acceptance.py")),
               "--evidence", str(view), "--require-complete"]
    with (output / "acceptance.log").open("w") as log:
        result = subprocess.run(command, cwd=args.root, stdout=log, stderr=subprocess.STDOUT)
    exit_code = complete_exit(result.returncode, historical_bound)
    publish_json(output / "outcome.json", {"command": command, "legacy_exit": result.returncode, "exit": exit_code,
                 "historical_import_binding": summary["historical_import_binding"],
                 "boundary": "Complete gate failures retained; missing historical binding cannot yield success"})
    raise SystemExit(exit_code)


if __name__ == "__main__":
    main()
