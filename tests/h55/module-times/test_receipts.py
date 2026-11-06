import importlib.util
import pathlib
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/receipts.py"
spec = importlib.util.spec_from_file_location("receipts", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class Receipts(unittest.TestCase):
    def good(self):
        return [{"path": "Solidity/A.lean", "status": "ok", "fresh": True, "elapsed_seconds": 300}]

    def check_bad(self, rows, inventory=None):
        self.assertTrue(module.validate(inventory if inventory is not None else ["Solidity/A.lean"], rows))

    def test_boundary_and_coverage(self):
        self.assertEqual([], module.validate(["Solidity/A.lean"], self.good()))
        self.check_bad([])
        self.check_bad(self.good() * 2)
        self.check_bad(self.good(), ["Solidity/A.lean", "Bridge/B.lean"])
        self.check_bad(self.good(), [])
        self.check_bad(self.good(), ["Solidity/A.lean", "Solidity/A.lean"])
        self.check_bad(self.good() + [{**self.good()[0], "path": "Bridge/B.lean"}])

    def test_fail_closed(self):
        for field, values in {"status": ["timeout", "error", None], "fresh": [False, 1, None],
                              "elapsed_seconds": [300.001, -1, None, True, "1", float("nan"), float("inf")]}.items():
            for value in values:
                with self.subTest(field=field, value=value):
                    self.check_bad([{**self.good()[0], field: value}])
        for path in ["../A.lean", "/A.lean", "A//B.lean", "A/./B.lean", "A\\B.lean", "A.txt"]:
            self.check_bad([{**self.good()[0], "path": path}])
        self.check_bad(None)


if __name__ == "__main__":
    unittest.main()
