#!/usr/bin/env python3
"""Recover the frozen lexical census from Git; never assert kernel/proof coverage.

The successor live tree may differ from the audit base. This separate recovery
path preserves the inherited census and acceptance guards unchanged. Bulk output
is external, immutable per run, and bound to the authenticated final-member scope.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
from census import BASE, generate
from bulk_inputs import bulk_bytes

MEMBER_HEAD = "4abcd439b60c63a6f02e91115599e6a730cd9bc9"
SCOPE_SHA256 = "c6d26b9f50936dec304b19e226e069be8f9f9f6e4229ac016cb73b156caf6c92"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git_blob(repo, revision, path):
    return subprocess.check_output(["git", "show", revision + ":" + path], cwd=repo)


def safe_path(path):
    value = PurePosixPath(path)
    if value.is_absolute() or ".." in value.parts or str(value) != path:
        raise ValueError("noncanonical snapshot path: " + path)
    if not path.startswith(("Solidity/", "docs/module-map/")) or "\\" in path:
        raise ValueError("outside frozen source scope: " + path)
    return path


def snapshot_entries(scope):
    if scope["base"] != BASE:
        raise ValueError("unexpected frozen base")
    entries = scope["module_maps"] + scope["mapped_sources"]
    names = [safe_path(row["path"]) for row in entries]
    if len(set(names)) != len(names):
        raise ValueError("duplicate snapshot path")
    return entries


def validate_census(scope, census):
    expected = {row["path"]: row["sha256"] for row in scope["mapped_sources"]}
    actual = {row["path"]: row["sha256"] for row in census["sources"]}
    if actual != expected or len(actual) != len(census["sources"]):
        raise ValueError("frozen census source roster/hash mismatch")
    if census["missing_module_paths"]:
        raise ValueError("missing mapped source")
    if len(census["declarations"]) != scope["source_declarations"]:
        raise ValueError("frozen declaration count mismatch")
    if census["counts"]["joint_witnesses_verified"] != 0:
        raise ValueError("lexical recovery must not claim proof coverage")


def recover(repo, output):
    repo, output = repo.resolve(), output.resolve()
    if output.is_relative_to(repo):
        raise ValueError("H44: output must be outside repository")
    scope_bytes = bulk_bytes("frozen_scope")
    if sha(scope_bytes) != SCOPE_SHA256:
        raise ValueError("authenticated member scope checksum mismatch")
    scope = json.loads(scope_bytes)
    entries = snapshot_entries(scope)
    subprocess.run(["git", "merge-base", "--is-ancestor", MEMBER_HEAD, "HEAD"],
                   cwd=repo, check=True)
    output.mkdir(parents=True, exist_ok=False)
    drift = []
    with tempfile.TemporaryDirectory(prefix="h62-frozen-census-", dir=output) as name:
        snapshot = Path(name)
        for row in entries:
            path = row["path"]
            data = git_blob(repo, BASE, path)
            if sha(data) != row["sha256"]:
                raise ValueError("frozen blob mismatch: " + path)
            target = snapshot / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            live = repo / path
            current = sha(live.read_bytes()) if live.is_file() else None
            if current != row["sha256"]:
                drift.append({"path": path, "frozen_sha256": row["sha256"],
                              "live_sha256": current})
        census = generate(snapshot)
        validate_census(scope, census)
    encoded = (json.dumps(census, indent=2, ensure_ascii=False) + "\n").encode()
    if sha(encoded) != scope["source_census_sha256"]:
        raise ValueError("recovered census differs from retired worker digest")
    (output / "source-census.json").write_bytes(encoded)
    result = {"schema_version": 1, "member_head": MEMBER_HEAD, "base": BASE,
              "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo,
                                               text=True).strip(),
              "scope_sha256": SCOPE_SHA256, "driver_sha256": sha(Path(__file__).read_bytes()),
              "source_census_sha256": sha(encoded), "counts": census["counts"],
              "live_drift": drift, "live_drift_count": len(drift),
              "boundary": "Lexical recovery only; no kernel export, proof, semantic or runtime acceptance"}
    (output / "recovery.json").write_text(json.dumps(result, indent=2) + "\n")
    files = ["source-census.json", "recovery.json"]
    (output / "SHA256SUMS").write_text("".join(
        sha((output / name).read_bytes()) + "  " + name + "\n" for name in files))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    result = recover(args.root, args.out)
    print(json.dumps({k: v for k, v in result.items() if k != "live_drift"}, sort_keys=True))


if __name__ == "__main__":
    main()
