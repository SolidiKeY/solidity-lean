import copy
import importlib.util
import pathlib
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/inventory_gate.py"
spec = importlib.util.spec_from_file_location("inventory_gate", path)
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class InventoryGate(unittest.TestCase):
    def setUp(self):
        self.current = [{"path": "Solidity/A.lean", "sha256": "a" * 64},
                        {"path": "Bridge/tests/B.lean", "sha256": "b" * 64}]
        self.rows = [{**self.current[0], "context": "root", "method": "module"},
                     {**self.current[1], "context": "bridge", "method": "file-check"}]

    def test_exact_and_missing_duplicate_extra(self):
        self.assertEqual([], gate.validate(self.current, self.rows))
        for rows in [[], self.rows[:1], self.rows + [self.rows[0]],
                     self.rows + [{**self.rows[0], "path": "Solidity/C.lean"}]]:
            with self.subTest(rows=rows):
                self.assertTrue(gate.validate(self.current, rows))

    def test_unresolved_forged_and_malformed(self):
        for key, value in [("sha256", "c" * 64), ("sha256", None), ("context", "review"),
                           ("context", None), ("method", "exclude"), ("method", None)]:
            rows = copy.deepcopy(self.rows)
            rows[0][key] = value
            with self.subTest(key=key, value=value):
                self.assertTrue(gate.validate(self.current, rows))
        self.assertTrue(gate.validate([], self.rows))
        self.assertTrue(gate.validate(self.current + [self.current[0]], self.rows))
        self.assertTrue(gate.validate(self.current, [None]))


if __name__ == "__main__":
    unittest.main()
