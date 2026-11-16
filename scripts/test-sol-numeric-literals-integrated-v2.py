"""Guard registration transport overreach and acceptance before owner approval."""
import copy
from contextlib import contextmanager
import hashlib
import os
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
import types
from unittest.mock import patch

PATH = Path(__file__).with_name("check-sol-numeric-literals-integrated-v2.py")
spec = importlib.util.spec_from_file_location("numeric_v2", PATH)
v2 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v2)


def source_identity():
    def git(*args):
        return subprocess.check_output(["git", "--no-optional-locks", *args], cwd=v2.ROOT)
    index = Path(git("rev-parse", "--git-path", "index").decode().strip())
    if not index.is_absolute():
        index = v2.ROOT / index
    return (git("rev-parse", "HEAD"), git("branch", "--show-current"),
            git("status", "--porcelain"), hashlib.sha256(index.read_bytes()).hexdigest())


@contextmanager
def branch_fixture():
    """Run real CLI guards on committed bytes without changing the caller's branch."""
    before = source_identity()
    env = dict(os.environ, GIT_TERMINAL_PROMPT="0", PYTHONDONTWRITEBYTECODE="1")
    for key in ("GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE",
                "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES"):
        env.pop(key, None)
    with tempfile.TemporaryDirectory(prefix="numeric-v2-branch-fixture-") as tmp:
        fixture = Path(tmp) / "checkout"
        def git(*args):
            return subprocess.run(["git", *args], env=env, capture_output=True, text=True, check=True)
        try:
            git("clone", "--quiet", "--shared", "--no-checkout", str(v2.ROOT), str(fixture))
            git("-C", str(fixture), "checkout", "--quiet", "-B",
                "codex/solidity-sol2-20261104/numeric-literals", before[0].decode().strip())
            for path in v2.CONTROL_FILES | set(v2.FROZEN):
                if (fixture / path).read_bytes() != (v2.ROOT / path).read_bytes():
                    raise AssertionError("CLI fixture differs from current committed controls: " + path)
            yield fixture, env
        finally:
            if source_identity() != before:
                raise AssertionError("branch fixture modified caller HEAD, branch, index or status")


def fixture_cli(fixture, env, *args):
    return subprocess.run(["python3", "-B", str(fixture / PATH.relative_to(v2.ROOT)), *args],
                          cwd=fixture, env=env, capture_output=True, text=True)


class RegistrationTransport(unittest.TestCase):
    def setUp(self):
        self.registration = json.loads((v2.ROOT / v2.REGISTRATION).read_bytes())
        self.root = v2.blob("Solidity.lean")
        self.module_map = v2.blob("docs/module-map/frontend.md")
        self.fragment = v2.blob(v2.FRAGMENT)
        self.modules = [line.split()[1] for line in self.root.decode().splitlines()
                        if line.startswith("import Solidity.Frontend.NumericLiteralProofs.")]

    def verify(self, **changes):
        args = dict(root=self.root, module_map=self.module_map, fragment=self.fragment,
                    registration=self.registration, modules=self.modules)
        args.update(changes)
        return v2.verify_registration(**args)

    def test_exact_candidate_and_two_field_projection(self):
        before = copy.deepcopy(self.registration)
        result = self.verify()
        self.assertEqual(self.registration, before)
        self.assertEqual({k for k in before if result[k] != before[k]},
                         {"desired_root_sha256", "desired_module_map_sha256"})
        self.assertEqual(result["desired_root_sha256"], v2.NEW_ROOT)
        self.assertEqual(result["desired_module_map_sha256"], v2.NEW_MAP)

    def test_original_pins_cannot_be_repinned(self):
        for key in ("desired_root_sha256", "desired_module_map_sha256"):
            bad = copy.deepcopy(self.registration)
            bad[key] = "0" * 64
            with self.assertRaisesRegex(ValueError, "original registration pins"):
                self.verify(registration=bad)

    def test_exact_root_map_fragment_bytes(self):
        for field in ("root", "module_map", "fragment"):
            with self.assertRaisesRegex(ValueError, "hash differs"):
                self.verify(**{field: getattr(self, field) + b"\n"})

    def test_all_rows_required_even_with_exact_artifacts(self):
        for rows in (self.registration["module_map_rows_to_add"][:-1],
                     ["changed"] + self.registration["module_map_rows_to_add"][1:]):
            bad = copy.deepcopy(self.registration)
            bad["module_map_rows_to_add"] = rows
            with self.assertRaisesRegex(ValueError, "34 exact"):
                self.verify(registration=bad)

    def test_all_imports_required_once(self):
        for modules in (self.modules[:-1], self.modules[:-1] + [self.modules[0]],
                        self.modules[:-1] + ["Solidity.Frontend.NumericLiteralProofs.Unknown"]):
            with self.assertRaisesRegex(ValueError, "42 exact"):
                self.verify(modules=modules)

    def test_every_frozen_input_is_guarded(self):
        v2.verify_frozen()
        for changed in v2.FROZEN:
            def read(path):
                raw = (v2.ROOT / path).read_bytes()
                return raw + b"\n" if path == changed else raw
            with self.assertRaisesRegex(ValueError, "frozen file changed"):
                v2.verify_frozen(read)

    def test_runtime_authority_and_scope_stay_separate(self):
        original = (v2.ROOT / v2.V1).read_bytes()
        v1 = v2.load_v1()
        self.assertEqual(v1.APPROVED_MASTER, v2.CANDIDATE_MASTER)
        self.assertEqual(v1.RUNTIME_APPROVED_MASTER, "0781d0b90cfa2773f6304a5da5390eaa7c8c8538")
        _, pair = v1.runtime_manifest()
        self.assertEqual(pair["serial_flag"], "-j1")
        self.assertFalse(pair["full_acceptance"])
        self.assertEqual(v1.CONTROL_FILES, v2.CONTROL_FILES | {
            "scripts/check-sol-numeric-literals-integrated.py",
            "scripts/test-sol-numeric-literals-integrated.py"})
        self.assertEqual((v2.ROOT / v2.V1).read_bytes(), original)

    def test_unapproved_and_wrong_master_refuse_acceptance(self):
        for approved in (None, "0" * 40):
            with patch.object(v2, "APPROVED_MASTER", approved):
                with self.assertRaisesRegex(ValueError, "approval pending"):
                    v2.require_approval()

    def test_execute_refuses_before_creating_outputs(self):
        with self.assertRaisesRegex(ValueError, "acceptance is disabled"):
            v2.execute(None, None, {}, None, None, True, False)

    def test_private_projection_delegation_records_failure_without_credit(self):
        v1 = v2.load_v1()
        projected = self.verify()
        original_folder = v1.Folder
        original = types.SimpleNamespace(validate_committed_inputs=lambda: None)
        with tempfile.TemporaryDirectory() as tmp:
            evidence, output = Path(tmp) / "input", Path(tmp) / "new-output"
            evidence.mkdir()
            manifest = output / "acceptance.h309.json"
            def staged(*args):
                output.mkdir()
                manifest.write_text("{}")
            def refuse(*args):
                v1.stage(evidence, output)
                folder = v1.Folder(v2.ROOT, output, manifest)
                self.assertEqual(json.loads((folder / "registration.json").read_text()), projected)
                self.assertEqual(folder / "evidence/x", output / "x")
                (output / "input-binding.json").write_text("{}")
                raise ValueError("original final gate refusal")
            with patch.object(v2, "APPROVED_MASTER", v2.CANDIDATE_MASTER), patch.object(v1, "stage", staged), patch.object(v1, "execute", refuse):
                with self.assertRaisesRegex(ValueError, "original final gate refusal"):
                    v2.execute(v1, original, projected, evidence, output, False, False)
            self.assertIs(v1.Folder, original_folder)
            record = json.loads((output / "registration-transport.json").read_text())
            self.assertTrue(record["transport_record_only_not_acceptance"])
            self.assertEqual(set(record["v2_control_sha256"]), v2.CONTROL_FILES)

    def test_registration_change_during_delegate_is_refused(self):
        v1 = v2.load_v1()
        projected = self.verify()
        original = types.SimpleNamespace(validate_committed_inputs=lambda: None)
        with tempfile.TemporaryDirectory() as tmp, patch.object(v2, "APPROVED_MASTER", v2.CANDIDATE_MASTER):
            with patch.object(v1, "execute", return_value=0), patch.object(v2, "registration_pair", return_value={}):
                with self.assertRaisesRegex(ValueError, "changed during validation"):
                    v2.execute(v1, original, projected, Path(tmp) / "input", Path(tmp) / "output", True, False)

    def test_rejected_existing_and_overlapping_outputs_are_unchanged(self):
        v1 = v2.load_v1()
        original = types.SimpleNamespace(validate_committed_inputs=lambda: None)
        with tempfile.TemporaryDirectory() as tmp:
            parent = Path(tmp)
            evidence, existing = parent / "input", parent / "existing"
            for folder in (evidence, existing):
                folder.mkdir()
                (folder / "input-binding.json").write_bytes(b"old binding")
                (folder / "registration-transport.json").write_bytes(b"old record")
            before = {str(p): p.read_bytes() for p in parent.rglob("*") if p.is_file()}
            for output in (existing, evidence, evidence / "nested", parent):
                with patch.object(v2, "APPROVED_MASTER", v2.CANDIDATE_MASTER), patch.object(v1, "execute") as delegate:
                    with self.assertRaises(ValueError):
                        v2.execute(v1, original, self.verify(), evidence, output, True, False)
                    delegate.assert_not_called()
                self.assertEqual({str(p): p.read_bytes() for p in parent.rglob("*") if p.is_file()}, before)

    def test_failed_staging_cannot_overwrite_preexisting_binding_record(self):
        v1 = v2.load_v1()
        original = types.SimpleNamespace(validate_committed_inputs=lambda: None)
        with tempfile.TemporaryDirectory() as tmp:
            evidence, output = Path(tmp) / "input", Path(tmp) / "output"
            evidence.mkdir()
            def fail_stage(*args):
                output.mkdir()
                (output / "input-binding.json").write_bytes(b"unowned binding")
                (output / "registration-transport.json").write_bytes(b"unowned record")
                raise ValueError("stage failed")
            def delegate(*args):
                v1.stage(evidence, output)
            with patch.object(v2, "APPROVED_MASTER", v2.CANDIDATE_MASTER), patch.object(v1, "stage", fail_stage), patch.object(v1, "execute", delegate):
                with self.assertRaisesRegex(ValueError, "stage failed"):
                    v2.execute(v1, original, self.verify(), evidence, output, True, False)
            self.assertEqual((output / "registration-transport.json").read_bytes(), b"unowned record")

    def test_uncommitted_or_missing_controls_are_refused(self):
        raw = {p: (v2.ROOT / p).read_bytes() for p in v2.CONTROL_FILES}
        for changed in raw:
            with self.assertRaisesRegex(ValueError, "untracked or differs"):
                v2.verify_controls(lambda p: raw[p] + (b"change" if p == changed else b""), raw.__getitem__)
            with self.assertRaises(KeyError):
                v2.verify_controls(raw.__getitem__, lambda p: {k: v for k, v in raw.items() if k != changed}[p])

    def test_diagnostic_is_explicitly_unbound(self):
        with branch_fixture() as (fixture, env):
            result = fixture_cli(fixture, env, "--proposal-only")
            self.assertEqual(result.returncode, 0, result.stderr)
        record = json.loads(result.stdout)
        self.assertIsNone(record["approved_master"])
        self.assertFalse(record["full_acceptance"])
        self.assertNotIn("approved_master", record["scope"])
        self.assertIn("diagnostic-not-acceptance", record["scope"]["mode"])

    def test_full_cli_cannot_claim_unbound_acceptance(self):
        with branch_fixture() as (fixture, env):
            result = fixture_cli(fixture, env)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("approval pending", result.stderr)

    def test_real_cli_still_rejects_wrong_branch(self):
        with branch_fixture() as (fixture, env):
            subprocess.run(["git", "checkout", "--quiet", "--detach"], cwd=fixture,
                           env=env, check=True, capture_output=True)
            result = fixture_cli(fixture, env, "--proposal-only")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("wrong original branch identity", result.stderr)


if __name__ == "__main__":
    unittest.main()
