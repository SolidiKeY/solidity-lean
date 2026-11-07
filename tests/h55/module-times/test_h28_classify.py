"""Guard regression: H28 mutation rows lose phase or source identity."""
import hashlib
import importlib.util
import json
import pathlib
import tempfile
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/h28_classify.py"
spec = importlib.util.spec_from_file_location("h28_classify", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class H28Classification(unittest.TestCase):
    def test_private_harness_accepts_only_direct_namespace_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            (root / "tests/h28-sol/mutation-testing/manifests").mkdir(parents=True)
            source = root / "tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/Nested/A.lean"
            source.parent.mkdir(parents=True)
            source.write_text("#check 1\n")
            row = {"path": str(source.relative_to(root)), "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            with self.assertRaisesRegex(ValueError, "outside harness discovery"):
                module.classify(root, {"rows": [row]})
            direct = source.parent.parent / "A.lean"
            source.rename(direct)
            row["path"] = str(direct.relative_to(root))
            self.assertEqual("Solidity.Assurance.NonVacuityH28.A", module.classify(root, {"rows": [row]})[0]["module"])

    def test_manifest_roles_are_retained_and_changed_source_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            source = root / "tests/h28-sol/mutation-testing/oracles/Mutant.lean"
            source.parent.mkdir(parents=True)
            source.write_text("import Fixture\n")
            manifests = root / "tests/h28-sol/mutation-testing/manifests"
            manifests.mkdir(parents=True)
            rel = str(source.relative_to(root))
            (manifests / "case.json").write_text(json.dumps({"cases": [{"id": "case", "kind": "mutant", "witness": rel}]}))
            row = {"path": rel, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            record = module.classify(root, {"rows": [row]})[0]
            self.assertEqual("witness", record["references"][0]["role"])
            self.assertEqual(hashlib.sha256((manifests / "case.json").read_bytes()).hexdigest(), record["references"][0]["manifest_sha256"])
            self.assertEqual("tests/h28-sol/mutation-testing/tools/runner.py", record["driver"])
            self.assertIn("phase dependent", record["expected"])
            self.assertEqual(row, record["candidate"])
            source.write_text("changed")
            with self.assertRaises(ValueError):
                module.classify(root, {"rows": [row]})
            source.write_text("import Fixture\n")
            (manifests / "case.json").write_text(json.dumps({"cases": []}))
            with self.assertRaises(ValueError):
                module.classify(root, {"rows": [row]})


if __name__ == "__main__":
    unittest.main()
