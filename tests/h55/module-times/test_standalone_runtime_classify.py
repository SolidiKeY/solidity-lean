"""Guard regression: held or runtime-only fixtures become accepted proofs."""
import hashlib
import importlib.util
import pathlib
import tempfile
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/standalone_runtime_classify.py"
spec = importlib.util.spec_from_file_location("standalone_runtime_classify", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class RuntimeFixtureClassification(unittest.TestCase):
    def test_staged_g49_remains_unresolved(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            source = root / module.G49 / "staging/CalculusControls.lean"
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            entry = {"path": str(source.relative_to(root)), "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            row = module.classify(root, {"rows": [entry]})[0]
            self.assertEqual("staged-snapshot", row["role"])
            self.assertEqual("unresolved-staged-snapshot", row["driver_reference"])
            self.assertEqual("unresolved per current invocation", row["expected_outcome"])

    def test_held_source_is_not_runtime_driver_and_drift_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            source = root / module.YUL / "held/FailurePhysical.lean"
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            entry = {"path": str(source.relative_to(root)), "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            row = module.classify(root, {"rows": [entry]})[0]
            self.assertEqual("held-source-producer-unresolved", row["role"])
            self.assertEqual("unresolved", row["driver_reference"])
            self.assertEqual("unresolved per current invocation", row["expected_outcome"])
            self.assertNotIn("--run driver may print", row["side_effects"])
            unknown = root / module.YUL / "UnknownDriver.lean"
            unknown.write_text("def main := pure ()\n")
            unknown_entry = {"path": str(unknown.relative_to(root)), "sha256": hashlib.sha256(unknown.read_bytes()).hexdigest()}
            with self.assertRaisesRegex(ValueError, "unreviewed Yul"):
                module.classify(root, {"rows": [unknown_entry]})
            source.write_text("changed")
            with self.assertRaises(ValueError):
                module.classify(root, {"rows": [entry]})


if __name__ == "__main__":
    unittest.main()
