"""Guard regression: output-writing fixtures lose their execution warnings."""
import hashlib
import importlib.util
import pathlib
import tempfile
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/h62_fixture_classify.py"
spec = importlib.util.spec_from_file_location("h62_fixture_classify", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class FixtureClassification(unittest.TestCase):
    def test_abi_vector_output_and_unknown_name(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            source = root / module.ABI / "RuntimeVectors.lean"
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            entry = {"path": str(source.relative_to(root)), "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            row = module.classify(root, {"rows": [entry]})[0]
            self.assertEqual("vector-output", row["role"])
            self.assertIn("external extractor", row["side_effects"])
            unknown = source.parent / "Unknown.lean"
            source.rename(unknown)
            entry["path"] = str(unknown.relative_to(root))
            with self.assertRaisesRegex(ValueError, "unreviewed ABI"):
                module.classify(root, {"rows": [entry]})

    def test_closed_telescope_role_does_not_imply_runtime_witness(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            source = root / module.CALCULUS / "JoinWalkWitnesses.lean"
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            entry = {"path": str(source.relative_to(root)), "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            row = module.classify(root, {"rows": [entry]})[0]
            self.assertEqual("closed-telescope-check", row["role"])
            self.assertEqual("unresolved per invocation", row["auxiliary_inputs"])

    def test_export_side_effect_and_source_drift(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            source = root / module.G25 / "BoundaryVectors.lean"
            source.parent.mkdir(parents=True)
            source.write_text("import Lean\n")
            entry = {"path": str(source.relative_to(root)), "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            row = module.classify(root, {"rows": [entry]})[0]
            self.assertEqual("external-vector-export", row["role"])
            self.assertIn("writes fixed", row["side_effects"])
            self.assertEqual("unresolved per invocation", row["auxiliary_inputs"])
            kernel = source.parent / "KernelCensus.lean"
            kernel.write_text("import Lean\n")
            kernel_entry = {"path": str(kernel.relative_to(root)), "sha256": hashlib.sha256(kernel.read_bytes()).hexdigest()}
            effects = module.classify(root, {"rows": [kernel_entry]})[0]["side_effects"]
            self.assertIn("kernel-census-v424.json", effects)
            self.assertIn("premise-structures-v424.json", effects)
            source.write_text("changed")
            with self.assertRaises(ValueError):
                module.classify(root, {"rows": [entry]})
            source.write_text("import Lean\n")
            with self.assertRaises(ValueError):
                module.classify(root, {"rows": [entry, entry]})


if __name__ == "__main__":
    unittest.main()
