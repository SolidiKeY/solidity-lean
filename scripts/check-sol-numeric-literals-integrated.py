#!/usr/bin/env python3
"""H296 integrated v1: guard unauthorized inherited-byte and local-scope drift.

The original checker remains byte-identical and independently failing. Only its
foreign-publication comparison is transported to the exact approved master.
All original proof pins, checks and final requirements still execute. Private
records are copied to a new external output tree; no evidence is restored here.
--scope-only checks integration identity, never implementation or acceptance.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import types

ROOT = Path(__file__).resolve().parents[1]
APPROVED_MASTER = "34950767333d88b3273b98500ea43e23cdaea069"
BRANCH = "codex/solidity-sol2-20261104/numeric-literals"
CONTROL_FILES = {"scripts/check-sol-numeric-literals-integrated.py",
                 "scripts/test-sol-numeric-literals-integrated.py"}
LEGACY = "scripts/check-sol-numeric-literals.py"
PACKET = "tests/sol-numeric-literals/packetlib.py"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_legacy():
    # Read source directly, not a possibly older Python bytecode cache.
    modules = []
    for name, path in (("packetlib", PACKET), ("numeric_original", LEGACY)):
        raw = (ROOT / path).read_bytes()
        approved = subprocess.check_output(["git", "show", APPROVED_MASTER + ":" + path], cwd=ROOT)
        require(raw == approved, "original checker/helper differs from H296 master: " + path)
        module = types.ModuleType(name)
        module.__file__ = str(ROOT / path)
        previous = sys.modules.get("packetlib")
        if modules:
            sys.modules["packetlib"] = modules[0]
        try:
            exec(compile(raw, str(ROOT / path), "exec"), module.__dict__)
        finally:
            if previous is None:
                sys.modules.pop("packetlib", None)
            else:
                sys.modules["packetlib"] = previous
        modules.append(module)
    return modules[-1]


def permitted(original, path):
    return original.permitted(path) or path in CONTROL_FILES


def foreign_guard(foreign, untracked, tree=None):
    require(not set(foreign).intersection(untracked), "untracked foreign write")
    if foreign:
        command = ["git", "diff", "--quiet", APPROVED_MASTER]
        if tree:
            command.append(tree)
        result = subprocess.run(command + ["--", *sorted(foreign)], cwd=ROOT)
        require(result.returncode == 0, "foreign work differs from H296 approved master")


def changed_paths(legacy_changed, tree=None):
    target = [tree] if tree else []
    current = set(git("diff", "--name-only", "--no-renames", APPROVED_MASTER, *target, "--").splitlines())
    return legacy_changed(tree) | current


def scope(original):
    require(git("branch", "--show-current") == BRANCH, "wrong original branch identity")
    subprocess.run(["git", "merge-base", "--is-ancestor", APPROVED_MASTER, "HEAD"], cwd=ROOT, check=True)
    # Include all files; no older coordinator-root exception can bypass this.
    changed = changed_paths(original.changed_paths)
    outside = {p for p in changed if not permitted(original, p)}
    foreign_guard(outside, set(git("ls-files", "--others", "--exclude-standard").splitlines()))
    return {"approved_master": APPROVED_MASTER, "head": git("rev-parse", "HEAD"),
            "mode": "scope-only-not-acceptance", "foreign_paths_checked": len(outside)}


class Folder:
    def __init__(self, original, evidence):
        self.original, self.evidence = original, evidence

    def __fspath__(self):
        return str(self.original)

    def __truediv__(self, value):
        path = Path(value)
        if path.parts and path.parts[0] == "evidence":
            return self.evidence.joinpath(*path.parts[1:])
        return self.original / path


def input_hashes(directory):
    require(directory.is_dir() and not directory.is_symlink(), "private evidence directory required")
    result = {}
    for path in sorted(directory.rglob("*")):
        require(not path.is_symlink(), "evidence symlinks are not sealed inputs")
        if path.is_file():
            result[str(path.relative_to(directory))] = sha(path)
    return result


def stage(evidence, output):
    require(not output.exists() and not output.is_symlink() and
            not output.resolve().is_relative_to(ROOT), "new external output directory required")
    require(not evidence.resolve().is_relative_to(ROOT), "evidence must remain outside checkout")
    before = input_hashes(evidence)
    snapshot = output / "snapshot"
    snapshot.mkdir(parents=True)
    files = git("ls-files", "tests/sol-numeric-literals", "Solidity/Frontend/NumericLiteralProofs", LEGACY, *sorted(CONTROL_FILES)).splitlines()
    source_hashes = {}
    for name in files:
        path = Path(name)
        if path.parts[:3] == ("tests", "sol-numeric-literals", "evidence"):
            continue
        target = snapshot / path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / path, target)
        source_hashes[name] = sha(ROOT / path)
        require(sha(target) == source_hashes[name], "snapshot copy differs: " + name)
    target = snapshot / "tests/sol-numeric-literals/evidence"
    shutil.copytree(evidence, target)
    require(before == input_hashes(evidence) == input_hashes(target), "evidence changed during staging")
    return snapshot, before, source_hashes


def execute(original, evidence, output, implementation=False, self_test=False):
    head = git("rev-parse", "HEAD")
    snapshot, before, sources = stage(evidence, output)
    original_folder, original_run = original.FOLDER, original.run
    original_permitted = original.permitted
    original_h41 = original.validate_h41_cache_record
    original_foreign = original.validate_foreign_paths
    original_changed = original.changed_paths
    private_evidence = snapshot / "tests/sol-numeric-literals/evidence"
    redirected = {"tests/sol-numeric-literals/differential.py",
                  "tests/sol-numeric-literals/h35/validate-axioms.py"}

    def run(command):
        if len(command) > 1 and command[1] in redirected:
            command = [command[0], str(snapshot / command[1]), *command[2:]]
        return original_run(command)

    def h41(record):
        # H145 relocates the approved prepared manifest, not its bytes/pins.
        root = original.ROOT
        original.ROOT = snapshot
        try:
            return original_h41(record)
        finally:
            original.ROOT = root

    original.FOLDER = Folder(original_folder, private_evidence)
    original.run = run
    original.permitted = lambda p: original_permitted(p) or p in CONTROL_FILES
    original.validate_foreign_paths = foreign_guard
    original.changed_paths = lambda tree=None: changed_paths(original_changed, tree)
    original.validate_h41_cache_record = h41
    try:
        # No success, trust, registration, review, seal, budget or full gate is skipped.
        return original.check(implementation, self_test)
    finally:
        original.FOLDER, original.run = original_folder, original_run
        original.permitted, original.validate_foreign_paths = original_permitted, original_foreign
        original.validate_h41_cache_record = original_h41
        original.changed_paths = original_changed
        require(head == git("rev-parse", "HEAD") and
                all(sha(ROOT / p) == h for p, h in sources.items()), "checked code inputs changed")
        require(before == input_hashes(evidence), "private input evidence changed during validation")
        (output / "input-binding.json").write_text(json.dumps(
            {"head": git("rev-parse", "HEAD"), "approved_master": APPROVED_MASTER,
             "private_input_sha256": before, "code_input_sha256": sources}, sort_keys=True, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scope-only", action="store_true")
    parser.add_argument("--implementation", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--evidence-root", type=Path)
    parser.add_argument("--output-root", type=Path)
    args = parser.parse_args()
    original = load_legacy()
    report = scope(original)
    if args.scope_only:
        require(not args.implementation and not args.self_test, "scope-only cannot claim implementation checks")
        print(json.dumps(report, sort_keys=True))
        return 0
    require(args.evidence_root is not None and args.output_root is not None,
            "private --evidence-root and new --output-root required")
    return execute(original, args.evidence_root.resolve(), args.output_root.resolve(),
                   args.implementation, args.self_test)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, FileNotFoundError, subprocess.CalledProcessError) as exc:
        print("numeric-literals integrated: FAIL: " + str(exc), file=sys.stderr)
        raise SystemExit(1)
