#!/usr/bin/env python3
"""H296 integrated v1: guard unauthorized inherited-byte and local-scope drift.

The original checker remains byte-identical and independently failing. Its
foreign-publication comparison uses the H296 master; H309 separately transports
only the approved runtime cache-key field with identical serial arguments.
All original proof pins, checks and final requirements still execute. Private
records are copied to a new external output tree; no evidence is restored here.
--scope-only and --runtime-only are diagnostics, never acceptance.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import types
import tomllib

ROOT = Path(__file__).resolve().parents[1]
APPROVED_MASTER = "34950767333d88b3273b98500ea43e23cdaea069"
BRANCH = "codex/solidity-sol2-20261104/numeric-literals"
CONTROL_FILES = {"scripts/check-sol-numeric-literals-integrated.py",
                 "scripts/test-sol-numeric-literals-integrated.py"}
LEGACY = "scripts/check-sol-numeric-literals.py"
PACKET = "tests/sol-numeric-literals/packetlib.py"
RUNTIME_PATH = "tests/sol-numeric-literals/runtime/lakefile.toml"
RUNTIME_APPROVED_MASTER = "0781d0b90cfa2773f6304a5da5390eaa7c8c8538"
RUNTIME_OLD_MASTER = "3883c64ef750dd49acdb7d83adcdf0f101d42c6c"
RUNTIME_OLD_SHA256 = "3060ca5e6636a012763981beeaa15bea5421bf1cbb99ed87d8ed2ccd3639b3cf"
RUNTIME_NEW_SHA256 = "df9c19f566e10ebacf85ce4dce4997daff3b1cbc73d424a10d45f0dc1816fa90"
MANIFEST_PATH = "tests/sol-numeric-literals/acceptance.json"


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


def same_toml(left, right):
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return left.keys() == right.keys() and all(same_toml(left[k], right[k]) for k in left)
    if isinstance(left, list):
        return len(left) == len(right) and all(same_toml(a, b) for a, b in zip(left, right))
    return left == right


def serial_runtime_equivalent(old_raw, new_raw):
    old, new = tomllib.loads(old_raw.decode()), tomllib.loads(new_raw.decode())
    require("weakLeanArgs" not in old and "moreLeanArgs" not in new,
            "runtime transport permits only the one root-field rename")
    require(old.pop("moreLeanArgs", None) == new.pop("weakLeanArgs", None) == ["-j1"],
            "runtime transport must preserve the exact serial flag")
    require(same_toml(old, new), "other runtime TOML fields changed")


def check_runtime_pair(old_raw, new_raw):
    require(hashlib.sha256(old_raw).hexdigest() == RUNTIME_OLD_SHA256 and
            hashlib.sha256(new_raw).hexdigest() == RUNTIME_NEW_SHA256,
            "runtime bytes differ from H309 exact old/new pins")
    serial_runtime_equivalent(old_raw, new_raw)


def project_runtime_manifest(manifest):
    require(manifest["gate_scripts"][RUNTIME_PATH] == RUNTIME_OLD_SHA256,
            "original runtime manifest pin changed")
    projected = copy.deepcopy(manifest)
    projected["gate_scripts"][RUNTIME_PATH] = RUNTIME_NEW_SHA256
    return projected


def runtime_manifest():
    old = subprocess.check_output(["git", "show", RUNTIME_OLD_MASTER + ":" + RUNTIME_PATH], cwd=ROOT)
    approved = subprocess.check_output(["git", "show", RUNTIME_APPROVED_MASTER + ":" + RUNTIME_PATH], cwd=ROOT)
    current = (ROOT / RUNTIME_PATH).read_bytes()
    require(current == approved, "runtime differs from H309 approved master")
    check_runtime_pair(old, current)
    raw = (ROOT / MANIFEST_PATH).read_bytes()
    frozen = subprocess.check_output(["git", "show", RUNTIME_APPROVED_MASTER + ":" + MANIFEST_PATH], cwd=ROOT)
    require(raw == frozen, "original acceptance manifest changed")
    projected = project_runtime_manifest(json.loads(raw))
    transport = {"authority": "H309 (H57 runtime-only pair)",
                 "approved_master": RUNTIME_APPROVED_MASTER,
                 "old_sha256": RUNTIME_OLD_SHA256, "new_sha256": RUNTIME_NEW_SHA256,
                 "serial_flag": "-j1", "other_toml_fields_unchanged": True,
                 "original_manifest_sha256": hashlib.sha256(raw).hexdigest(),
                 "projected_field": "gate_scripts." + RUNTIME_PATH,
                 "full_acceptance": False}
    return projected, transport


class Folder:
    def __init__(self, original, evidence, manifest=None):
        self.original, self.evidence, self.manifest = original, evidence, manifest

    def __fspath__(self):
        return str(self.original)

    def __truediv__(self, value):
        path = Path(value)
        if path == Path("acceptance.json") and self.manifest is not None:
            return self.manifest
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
    evidence_tree, output_tree = evidence.resolve(), output.resolve()
    require(not output_tree.is_relative_to(evidence_tree) and
            not evidence_tree.is_relative_to(output_tree),
            "private input and output trees must not overlap")
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
    projected, transport = runtime_manifest()
    snapshot, before, sources = stage(evidence, output)
    manifest = snapshot / "tests/sol-numeric-literals/acceptance.h309.json"
    manifest.write_text(json.dumps(projected, indent=2) + "\n")
    (output / "runtime-transport.json").write_text(json.dumps(transport, indent=2) + "\n")
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

    original.FOLDER = Folder(original_folder, private_evidence, manifest)
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
             "private_input_sha256": before, "code_input_sha256": sources,
             "runtime_transport": transport, "projected_manifest_sha256": sha(manifest)}, sort_keys=True, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scope-only", action="store_true")
    parser.add_argument("--runtime-only", action="store_true")
    parser.add_argument("--implementation", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--evidence-root", type=Path)
    parser.add_argument("--output-root", type=Path)
    args = parser.parse_args()
    original = load_legacy()
    if args.runtime_only:
        require(not args.scope_only and not args.implementation and not args.self_test,
                "runtime-only cannot claim scope or acceptance checks")
        require(git("branch", "--show-current") == BRANCH, "wrong original branch identity")
        _, transport = runtime_manifest()
        transport["mode"] = "runtime-transport-only-not-acceptance"
        print(json.dumps(transport, sort_keys=True))
        return 0
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
