import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("mapping", ROOT / "scripts/h55/module-times/mapping.py")
mapping = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mapping)


class Mapping(unittest.TestCase):
    def test_contexts_and_unresolved(self):
        for path, context, module in [
            ("Solidity/Examples/Foo.lean", "root", "Solidity.Examples.Foo"),
            ("SoliditySlowExamples.lean", "root", "SoliditySlowExamples"),
            ("Bridge/SolidityBridge/Foo.lean", "bridge", "SolidityBridge.Foo"),
            ("Bridge/vendor/Loom/Foo.lean", "bridge-vendor", "Loom.Foo"),
            ("Bridge/vendor/Loom/DoNames'.lean", "bridge-vendor", "Loom.DoNames'"),
            ("tests/X.lean", "standalone-root-review", None),
            ("Bridge/tests/X.lean", "standalone-bridge-review", None),
            ("Solidity/invalid-name.lean", "root", None),
        ]:
            with self.subTest(path=path):
                result = mapping.candidate({"path": path})
                self.assertEqual((context, module), (result["context"], result["module"]))
                self.assertIn("review", result["resolution"])

    def test_no_row_dropped_and_collisions_reported(self):
        rows = mapping.census.census(ROOT)
        result = mapping.derive(rows)
        self.assertEqual([r["path"] for r in rows], [r["path"] for r in result])
        duplicated = mapping.derive([{"path": "Solidity/X.lean"}, {"path": "Solidity/X.lean"}])
        self.assertTrue(all(r["collision"] for r in duplicated))
        peers = mapping.derive([{"path": "Solidity/X.lean"},
                                {"path": "Bridge/vendor/Solidity/X.lean"},
                                {"path": "Bridge/Solidity/X.lean"},
                                {"path": "vendor/LeanTeX/Solidity/X.lean"}])
        self.assertEqual(["root", "bridge-vendor", "bridge", "root-vendor"], [r["context"] for r in peers])
        self.assertTrue(all(r["collision"] for r in peers))
        unique = mapping.derive([{"path": "Solidity/X.lean"},
                                 {"path": "Bridge/vendor/Solidity/Y.lean"}])
        self.assertTrue(all(not r["collision"] for r in unique))


if __name__ == "__main__":
    unittest.main()
