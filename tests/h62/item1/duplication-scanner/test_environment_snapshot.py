import copy
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
SCRIPT = ROOT / "scripts/h62/item1/duplication-scanner/observe_signature_environment.py"
spec = importlib.util.spec_from_file_location("h62_environment", SCRIPT)
observer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(observer)

def name(*parts):
    result = ["anonymous"]
    for part in parts:
        result = ["str", result, part]
    return result

def module(path, *parts):
    base = path.joinpath(*parts).with_suffix(".olean")
    return {"module": name(*parts), "importAll": True, "isExported": False,
            "isMeta": False, "irPhases": "all", "base": str(base),
            "base_real": str(base.resolve()), "server": str(base) + ".server",
            "server_present": False, "server_real": None, "private": str(base) + ".private",
            "private_present": False, "private_real": None}

class SnapshotControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "space ü"
        (self.root / "Pkg").mkdir(parents=True)
        (self.root / "Pkg/A.olean").write_bytes(b"A")
        (self.root / "Pkg/B.olean").write_bytes(b"B")
        a, b = module(self.root, "Pkg", "A"), module(self.root, "Pkg", "B")
        self.env = {"format": 1, "kind": "fixture-local-observation", "lean_version": "4.24.0",
                    "main_module": name("SignatureEnvironmentProbe"), "is_module": False,
                    "trust_level": 0, "search_path": [str(self.root), str(self.root)],
                    "direct_imports": [{k: a[k] for k in observer.IMPORT_FIELDS}],
                    "modules": [a, b]}

    def test_snapshot_rechecks_and_never_attests(self):
        snap = observer.capture_environment(self.env)
        self.assertEqual(len(snap["artifacts"]), 2)
        consumer = copy.deepcopy(self.env)
        consumer["main_module"] = name("SignatureObservedConsumer")
        result = observer.verify_observation(snap, consumer, copy.deepcopy(snap))
        self.assertEqual(result["environment_binding"], "unbound")
        forged = copy.deepcopy(snap)
        forged["artifacts"] = []
        with self.assertRaisesRegex(ValueError, "current artifacts"):
            observer.verify_observation(forged, consumer, copy.deepcopy(forged))
        (self.root / "Pkg/A.olean").write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "current artifacts"):
            observer.verify_observation(snap, consumer, copy.deepcopy(snap))

    def test_shadow_and_missing_first_root_fail_closed(self):
        other = Path(self.tmp.name) / "other"
        (other / "Pkg").mkdir(parents=True)
        (other / "Pkg/B.olean").write_bytes(b"later")
        env = copy.deepcopy(self.env)
        env["search_path"].append(str(other))
        with self.assertRaisesRegex(ValueError, "shadowed"):
            observer.capture_environment(env)
        (self.root / "Pkg/B.olean").unlink()
        with self.assertRaisesRegex(ValueError, "shadowed"):
            observer.capture_environment(env)

    def test_sidecars_are_observed_with_loader_condition(self):
        item = self.env["modules"][0]
        private = Path(item["private"])
        private.write_bytes(b"private")
        item["private_present"], item["private_real"] = True, str(private.resolve())
        first = observer.capture_environment(self.env)
        self.assertFalse(first["artifacts"][0]["private_loader_candidate"])
        server = Path(item["server"])
        server.write_bytes(b"server")
        with self.assertRaisesRegex(ValueError, "presence mismatch"):
            observer.capture_environment(self.env)
        item["server_present"], item["server_real"] = True, str(server.resolve())
        second = observer.capture_environment(self.env)
        self.assertTrue(second["artifacts"][0]["private_loader_candidate"])
        consumer = copy.deepcopy(self.env)
        consumer["main_module"] = name("SignatureObservedConsumer")
        with self.assertRaisesRegex(ValueError, "snapshots differ"):
            observer.verify_observation(first, consumer, second)

    def test_duplicate_missing_and_malformed_records_fail(self):
        env = copy.deepcopy(self.env)
        env["modules"].append(copy.deepcopy(env["modules"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            observer.capture_environment(env)
        env = copy.deepcopy(self.env)
        env["direct_imports"].append(copy.deepcopy(env["direct_imports"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            observer.capture_environment(env)
        env = copy.deepcopy(self.env)
        env["trust_level"] = True
        with self.assertRaisesRegex(ValueError, "environment header"):
            observer.capture_environment(env)
        env = copy.deepcopy(self.env)
        env["modules"][0]["module"] = ["num", ["anonymous"], 2]
        with self.assertRaisesRegex(ValueError, "unsupported module name"):
            observer.capture_environment(env)
        (self.root / "Pkg/A.olean").unlink()
        with self.assertRaises((ValueError, OSError)):
            observer.capture_environment(self.env)

    def test_symlink_target_change_is_not_equivalent(self):
        target1 = self.root / "first"
        target2 = self.root / "second"
        target1.write_bytes(b"one")
        target2.write_bytes(b"two")
        base = self.root / "Pkg/A.olean"
        base.unlink()
        os.symlink(target1, base)
        self.env["modules"][0]["base_real"] = str(target1.resolve())
        snap = observer.capture_environment(self.env)
        base.unlink()
        os.symlink(target2, base)
        consumer = copy.deepcopy(self.env)
        consumer["main_module"] = name("SignatureObservedConsumer")
        with self.assertRaises((ValueError, OSError)):
            observer.verify_observation(snap, consumer, copy.deepcopy(snap))

    def test_fixture_envelope_binds_logs_and_inputs_without_attesting(self):
        for item in ("SignatureFingerprint", "SignatureEnvironment"):
            (self.root / (item + ".olean")).write_bytes(item.encode())
            self.env["modules"].append(module(self.root, item))
        extras = {}
        for label in observer.REQUIRED_EXTRAS:
            if label == "fingerprint_olean":
                path = self.root / "SignatureFingerprint.olean"
            elif label == "environment_olean":
                path = self.root / "SignatureEnvironment.olean"
            elif label in {"fingerprint_source", "environment_source", "probe_source", "consumer_source", "record_checker", "expected_records"}:
                files = {"fingerprint_source": "SignatureFingerprint.lean",
                         "environment_source": "SignatureEnvironment.lean",
                         "probe_source": "SignatureEnvironmentProbe.lean",
                         "consumer_source": "SignatureObservedConsumer.lean",
                         "record_checker": "check_signature_records.py",
                         "expected_records": "signature-records.expected.jsonl"}
                path = ROOT / "tests/h62/item1/duplication-scanner" / files[label]
            elif label == "snapshot_tool":
                path = SCRIPT
            elif label == "driver":
                path = ROOT / "scripts/h62/item1/duplication-scanner/check_signature_fixture.sh"
            elif label == "lean_toolchain":
                path = ROOT / "lean-toolchain"
            else:
                path = self.root / label
                path.write_bytes(label.encode())
            extras[label] = path
        probe = self.root / "probe.log"
        probe.write_text(observer.PREFIX + json.dumps(self.env) + "\n")
        observed = copy.deepcopy(self.env)
        observed["main_module"] = name("SignatureObservedConsumer")
        expected = (ROOT / "tests/h62/item1/duplication-scanner/signature-records.expected.jsonl").read_text()
        consumer = self.root / "consumer.log"
        consumer.write_text(observer.PREFIX + json.dumps(observed) + "\n" + expected)
        capture = [sys.executable, "-B", str(SCRIPT), "capture", str(probe)]
        for label, path in sorted(extras.items()):
            capture += ["--extra", label + "=" + str(path)]
        snapshot = subprocess.check_output(capture)
        before, after = self.root / "before.json", self.root / "after.json"
        before.write_bytes(snapshot)
        after.write_bytes(snapshot)
        verify = [sys.executable, "-B", str(SCRIPT), "verify", str(before), str(probe),
                  str(consumer), str(probe), str(after)]
        result = json.loads(subprocess.check_output(verify))
        self.assertEqual(result["environment_binding"], "unbound")
        self.assertEqual(result["modules"], 4)
        swapped = dict(extras)
        swapped["fingerprint_source"] = extras["consumer_source"]
        bad_capture = [sys.executable, "-B", str(SCRIPT), "capture", str(probe)]
        for label, path in sorted(swapped.items()):
            bad_capture += ["--extra", label + "=" + str(path)]
        bad = self.root / "bad.json"
        bad.write_bytes(subprocess.check_output(bad_capture))
        bad_verify = [sys.executable, "-B", str(SCRIPT), "verify", str(bad), str(probe),
                      str(consumer), str(probe), str(bad)]
        self.assertNotEqual(subprocess.run(bad_verify, capture_output=True).returncode, 0)
        probe.write_text(probe.read_text() + " ")
        self.assertNotEqual(subprocess.run(verify, capture_output=True).returncode, 0)
        probe.write_text(observer.PREFIX + json.dumps(self.env) + "\n")
        extras["lean_command_path"].write_bytes(b"changed")
        self.assertNotEqual(subprocess.run(verify, capture_output=True).returncode, 0)

    def test_json_duplicate_and_nonfinite_refused(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            observer.json_load(b'{"a":1,"a":1}')
        with self.assertRaisesRegex(ValueError, "non-integer"):
            observer.json_load(b'{"a":NaN}')

if __name__ == "__main__":
    unittest.main()
