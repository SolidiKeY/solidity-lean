#!/usr/bin/env python3
"""Guard false registration acceptance from unrelated master ancestry or pin drift.

Unbound H314 candidate beside frozen H296/H309 v1. Diagnostics never grant
acceptance. Implementation/full modes require explicit owner-reviewed binding;
all legacy source, fixture, trust, resource and final-gate checks still run.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import types

ROOT = Path(__file__).resolve().parents[1]
CANDIDATE_MASTER = "36ba6149bc2e98d60ed689dc0aab9103a49541e8"
APPROVED_MASTER = None  # Q-NL-REG-TRANSPORT1: no acceptance freeze yet.
V1 = "scripts/check-sol-numeric-literals-integrated.py"
REGISTRATION = "tests/sol-numeric-literals/registration.json"
FRAGMENT = "docs/module-map/frontend.d/coord-numeric-registration.md"
CONTROL_FILES = {"scripts/check-sol-numeric-literals-integrated-v2.py",
                 "scripts/test-sol-numeric-literals-integrated-v2.py"}
FROZEN = {
    V1: "44c0655c3b0d194f96b82eb448b4e08a8fb94a9e3643abb931aabdd9a0e4b8d8",
    "scripts/test-sol-numeric-literals-integrated.py": "65cb5a160260696e82ead0ccaada800cb42a63ce5274f08162453bfdcd5cf3a1",
    "scripts/check-sol-numeric-literals.py": "7e66307eb9f5349d389e8a1f5cb03ddc162c915ab28adfc53e9326f7ca0191ab",
    "tests/sol-numeric-literals/packetlib.py": "ba29b2c5e4a0587254f09f3bd7268e82e5442728f8b180fcf3f2a9d626a64ca7",
    REGISTRATION: "a0324201d830eaabd1df05f313968fd2e625093d911e58970c304d2389c5d5b6",
    "tests/sol-numeric-literals/acceptance.json": "e7569c207f825784094a88dbfd17c54195b13969039f7923392230ac7bc199fd",
}
OLD_ROOT = "6f45c88cd68a1d4c38921b4d12188bd83fc18383db3e9fba976243a51e78336c"
OLD_MAP = "050a1b4d29b61884f32aaaff3ba75e41c30190064463b3ad7e891ca7605526fb"
NEW_ROOT = "50960627a97960d2d6e19541d313d3af4a80b06438545a13c6eb5393399596dc"
NEW_MAP = "6b433ce2249190d527d60f9d93ee043b9200af3ae864a87384d4ee3b40ae7e29"
FRAGMENT_SHA = "ea233d934dde92239f59a75071278134ed4f4831870abbfddb37d4ead26b9678"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def blob(path):
    return subprocess.check_output(["git", "show", CANDIDATE_MASTER + ":" + path], cwd=ROOT)


def verify_frozen(read=None):
    read = read or (lambda p: (ROOT / p).read_bytes())
    for path, expected in FROZEN.items():
        require(digest(read(path)) == expected, "frozen file changed: " + path)


def project_registration(registration):
    require(registration["desired_root_sha256"] == OLD_ROOT and
            registration["desired_module_map_sha256"] == OLD_MAP,
            "original registration pins changed")
    projected = copy.deepcopy(registration)
    projected["desired_root_sha256"] = NEW_ROOT
    projected["desired_module_map_sha256"] = NEW_MAP
    return projected


def verify_registration(root, module_map, fragment, registration, modules):
    require(digest(root) == NEW_ROOT and digest(module_map) == NEW_MAP and
            digest(fragment) == FRAGMENT_SHA, "candidate root/map/fragment hash differs")
    rows = fragment.decode().splitlines()
    require(rows == registration["module_map_rows_to_add"] and len(rows) == 34,
            "all 34 exact registration rows required")
    require(all(module_map.decode().splitlines().count(row) == 1 for row in rows),
            "registered row missing or duplicated")
    require(len(modules) == len(set(modules)) == 42 and
            all(root.decode().splitlines().count("import " + m) == 1 for m in modules),
            "all 42 exact numeric imports required once")
    return project_registration(registration)


def registration_pair():
    registration = json.loads((ROOT / REGISTRATION).read_bytes())
    modules = subprocess.check_output([
        "git", "ls-tree", "-r", "--name-only", CANDIDATE_MASTER, "--",
        "Solidity/Frontend/NumericLiteralProofs"], cwd=ROOT, text=True).splitlines()
    modules = [p.removesuffix(".lean").replace("/", ".") for p in modules if p.endswith(".lean")]
    for path in ("Solidity.lean", "docs/module-map/frontend.md", FRAGMENT):
        require((ROOT / path).read_bytes() == blob(path), "candidate bytes changed: " + path)
    return verify_registration((ROOT / "Solidity.lean").read_bytes(),
                               (ROOT / "docs/module-map/frontend.md").read_bytes(),
                               (ROOT / FRAGMENT).read_bytes(), registration, modules)


def require_approval():
    require(APPROVED_MASTER is not None and APPROVED_MASTER == CANDIDATE_MASTER,
            "H314 owner review/exact-master approval pending; acceptance is disabled")


def load_v1():
    verify_frozen()
    v1 = types.ModuleType("numeric_integrated_frozen_v1")
    v1.__file__ = str(ROOT / V1)
    exec(compile((ROOT / V1).read_bytes(), v1.__file__, "exec"), v1.__dict__)
    # Separate v2 adoption boundary; disk bytes and independently failing v1 stay frozen.
    v1.APPROVED_MASTER = CANDIDATE_MASTER
    v1.CONTROL_FILES = v1.CONTROL_FILES | CONTROL_FILES
    return v1


def verify_controls(read=None, committed=None):
    read = read or (lambda p: (ROOT / p).read_bytes())
    committed = committed or (lambda p: subprocess.check_output(["git", "show", "HEAD:" + p], cwd=ROOT))
    hashes = {}
    for path in sorted(CONTROL_FILES):
        raw = read(path)
        require(raw == committed(path), "v2 control is untracked or differs from HEAD: " + path)
        hashes[path] = digest(raw)
    return hashes


def output_preflight(evidence, output):
    source, target = evidence.resolve(), output.resolve()
    require(not source.is_relative_to(target) and not target.is_relative_to(source),
            "private input and output trees must not overlap")
    require(not output.exists() and not output.is_symlink() and not target.is_relative_to(ROOT),
            "new external output directory required")
    require(not source.is_relative_to(ROOT), "evidence must remain outside checkout")


def execute(v1, original, projected, evidence, output, implementation, self_test):
    require_approval()
    controls = verify_controls()
    original.validate_committed_inputs()
    output_preflight(evidence, output)
    folder, original_stage = v1.Folder, v1.stage
    staged = False

    def stage(*args):
        nonlocal staged
        result = original_stage(*args)
        staged = True
        return result

    class RegistrationFolder(folder):
        def __init__(self, original_folder, private_evidence, manifest=None):
            super().__init__(original_folder, private_evidence, manifest)
            require(manifest is not None, "private manifest required")
            self.registration = manifest.with_name("registration.h314.json")
            self.registration.write_text(json.dumps(projected, indent=2) + "\n")

        def __truediv__(self, path):
            return self.registration if Path(path) == Path("registration.json") else super().__truediv__(path)

    v1.Folder, v1.stage = RegistrationFolder, stage
    try:
        # Frozen v1 still performs its H309 pair, scope, proof and final checks.
        return v1.execute(original, evidence, output, implementation, self_test)
    finally:
        v1.Folder, v1.stage = folder, original_stage
        verify_frozen()
        require(verify_controls() == controls, "v2 controls changed during validation")
        require(registration_pair() == projected, "registration inputs changed during validation")
        if staged and (output / "input-binding.json").is_file():
            (output / "registration-transport.json").write_text(json.dumps({
                "authority": "H314 reviewed registration transport",
                "approved_master": APPROVED_MASTER,
                "root_sha256": NEW_ROOT, "map_sha256": NEW_MAP,
                "fragment_sha256": FRAGMENT_SHA, "v2_control_sha256": controls,
                "original_registration_sha256": FROZEN[REGISTRATION],
                "projected_registration_sha256": digest(json.dumps(projected, sort_keys=True).encode()),
                "transport_record_only_not_acceptance": True}, sort_keys=True, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proposal-only", action="store_true")
    parser.add_argument("--scope-only", action="store_true")
    parser.add_argument("--implementation", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--evidence-root", type=Path)
    parser.add_argument("--output-root", type=Path)
    args = parser.parse_args()
    require(not (args.proposal_only and args.scope_only), "choose one diagnostic")
    require(not ((args.proposal_only or args.scope_only) and (args.implementation or args.self_test)),
            "diagnostics cannot claim implementation or acceptance")
    v1 = load_v1()
    original = v1.load_legacy()
    scope = v1.scope(original)
    scope["candidate_master"] = scope.pop("approved_master")
    scope["mode"] = "candidate-scope-diagnostic-not-acceptance"
    projected = registration_pair()
    _, runtime = v1.runtime_manifest()
    if args.proposal_only or args.scope_only:
        print(json.dumps({"mode": "unbound-candidate-diagnostic-not-acceptance",
                          "full_acceptance": False, "approved_master": APPROVED_MASTER,
                          "candidate_master": CANDIDATE_MASTER, "scope": scope,
                          "projected_registration_sha256": digest(json.dumps(projected, sort_keys=True).encode()),
                          "runtime_transport": runtime}, sort_keys=True))
        return 0
    require_approval()
    require(args.evidence_root is not None and args.output_root is not None,
            "private evidence and new external output required")
    return execute(v1, original, projected, args.evidence_root.resolve(),
                   args.output_root.resolve(), args.implementation, args.self_test)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, FileNotFoundError, subprocess.CalledProcessError) as exc:
        print("numeric-literals integrated v2: FAIL: " + str(exc), file=sys.stderr)
        raise SystemExit(1)
