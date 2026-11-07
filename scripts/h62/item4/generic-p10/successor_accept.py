#!/usr/bin/env python3
"""Source-only P10 acceptance for the authenticated H82 successor.

The original branch-bound accept.py is unchanged. This entry point checks the
same frozen family/receipt on the explicitly assigned successor branch and
requires the exact retired final commit in its ancestry. It accepts no Lean,
semantic, migration, gas/fork, timing or package gate evidence.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import types

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FAMILY = Path("Bridge/SolidityBridge/RoadmapV15")
SUCCESSOR_BRANCH = "codex/solidity-parallel-20261103/executable-bytecode"
MEMBER_HEAD = "dcb2efa56558cfd7c056b8c8fcda724b9683750a"
RECEIPT = "tests/h62/item4/generic-p10/census-receipt.json"
SCANNER = "scripts/h62/item4/generic-p10/census.py"
BOUNDARY = "Frozen source reproduction only; no Lean, semantic, runtime, migration, timing or external acceptance."


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def regular_file(repo, relative):
    path = repo / relative
    for parent in (path, *path.parents):
        if parent == repo:
            break
        if parent.is_symlink():
            raise ValueError("symlink in frozen source path: " + str(relative))
    if not path.is_file():
        raise ValueError("missing regular source: " + str(relative))
    return path.read_bytes()


def authenticated_scanner(repo):
    # Compile the checked bytes rather than re-reading/importing a mutable path.
    raw = regular_file(repo, SCANNER)
    if raw != git(repo, "show", MEMBER_HEAD + ":" + SCANNER):
        raise ValueError("retired scanner changed")
    module = types.ModuleType("h82_authenticated_p10_census")
    module.__file__ = str(repo / SCANNER)
    exec(compile(raw, module.__file__, "exec"), module.__dict__)
    if module.BASE != BASE or module.FAMILY != FAMILY:
        raise ValueError("retired scanner base/family mismatch")
    return module, raw


def verify_inventory(raw, receipt, frozen, current, reproduced):
    """Verify all inventory content, not just counts or a supplied digest."""
    if sha(raw) != receipt["inventory_sha256"]:
        raise ValueError("inventory checksum differs from retired receipt")
    data = json.loads(raw)
    if data["base"] != BASE or receipt["base"] != BASE:
        raise ValueError("wrong frozen base")
    paths = [row["path"] for row in data["files"]]
    if not paths or paths != sorted(frozen) or set(current) != set(frozen):
        raise ValueError("frozen family file set differs")
    for row in data["files"]:
        path = row["path"]
        if row["source_sha256"] != sha(frozen[path]):
            raise ValueError("inventory has unpinned source: " + path)
        if current[path] != frozen[path]:
            raise ValueError("current source differs from frozen base: " + path)
    if data["summary"] != receipt["summary"]:
        raise ValueError("retired receipt summary differs")
    if reproduced != raw:
        raise ValueError("current census differs from frozen inventory")
    return data


def verify(repo, inventory):
    repo = repo.resolve()
    top = Path(git(repo, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    if top != repo:
        raise ValueError("repository root required")
    if git(repo, "branch", "--show-current").decode().strip() != SUCCESSOR_BRANCH:
        raise ValueError("wrong successor branch")
    for commit in (BASE, MEMBER_HEAD):
        subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor", commit, "HEAD"], check=True)
    receipt_raw = git(repo, "show", MEMBER_HEAD + ":" + RECEIPT)
    if regular_file(repo, RECEIPT) != receipt_raw:
        raise ValueError("retired receipt changed")
    scanner, scanner_raw = authenticated_scanner(repo)
    paths = git(repo, "ls-tree", "-r", "--name-only", BASE, "--", str(FAMILY)).decode().splitlines()
    paths = sorted(path for path in paths if path.endswith(".lean"))
    frozen = {path: git(repo, "show", BASE + ":" + path) for path in paths}
    current_paths = sorted(path.relative_to(repo).as_posix() for path in (repo / FAMILY).rglob("*.lean"))
    if current_paths != paths:
        raise ValueError("frozen family file set differs")
    current = {path: regular_file(repo, path) for path in current_paths}
    if git(repo, "diff", "--cached", "--name-only", BASE, "--", str(FAMILY)).strip():
        raise ValueError("staged frozen family differs")
    raw = inventory.read_bytes()
    reproduced = scanner.render(scanner.census(repo)).encode()
    data = verify_inventory(raw, json.loads(receipt_raw), frozen, current, reproduced)
    return {"schema_version": 1, "boundary": BOUNDARY,
            "successor_head": git(repo, "rev-parse", "HEAD").decode().strip(),
            "successor_branch": SUCCESSOR_BRANCH, "member_head": MEMBER_HEAD,
            "frozen_base": BASE, "receipt_sha256": sha(receipt_raw),
            "scanner_sha256": sha(scanner_raw),
            "verifier_sha256": sha(Path(__file__).read_bytes()),
            "inventory_sha256": sha(raw), "summary": data["summary"],
            "source_files_verified": len(frozen), "staged_family_unchanged": True,
            "whole_successor_write_scope_gate": "not performed; inherited branches and master are outside this source gate"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.resolve().is_relative_to(args.repo.resolve()):
        raise ValueError("H44: output must be outside repository")
    for parent in (args.output, *args.output.parents):
        if parent.is_symlink():
            raise ValueError("refusing symlink output path")
    result = verify(args.repo, args.inventory)
    with args.output.open("x") as out:
        out.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("SUCCESSOR_FROZEN_SOURCE_PASS: " + str(result["source_files_verified"]) + " files")
    print(BOUNDARY)


if __name__ == "__main__":
    main()
