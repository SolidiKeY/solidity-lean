import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]
def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts/h55/module-times" / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

census = load("census")
parser = load("lake_log")

class CensusParser(unittest.TestCase):
    def test_complete_tracked_tree_and_categories(self):
        rows = census.census(ROOT)
        import subprocess
        paths = subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"], cwd=ROOT).decode().split("\0")[:-1]
        self.assertEqual(sorted(paths), [r["path"] for r in rows])
        self.assertEqual("examples", census.classify("Solidity/Examples/X.lean"))
        self.assertEqual("bridge-control-review", census.classify("Bridge/tests/X.lean"))
        self.assertEqual("vendor-review", census.classify("Bridge/vendor/X.lean"))
        self.assertTrue(all(len(r["sha256"]) == 64 for r in rows))

    def test_duration_strictness(self):
        for value, expected in [("476ms", .476), ("2m 3s", 123), ("1.5m", 90), ("1h 1m 2s 3ms", 3662.003)]:
            self.assertAlmostEqual(expected, parser.seconds(value))
        for value in ["", "nonsense", "1s junk", "1s 2s", "1ms 1s", "NaNs", "1e5s", "1.2.3s", "-1s"]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                parser.seconds(value)

    def test_rows_and_malformed_rows(self):
        result = parser.parse("✔ [2/10] Built Solidity.A (2m 3s)\n✔ [3/10] Replayed Solidity.B (1s)\n✔ [4/10] Built Solidity.C (bad)\n")
        self.assertEqual(["Built", "Replayed"], [r["action"] for r in result["rows"]])
        self.assertEqual(123, result["rows"][0]["seconds"])
        self.assertEqual(1, len(result["errors"]))
        self.assertTrue(parser.parse("Built Solidity.A (1s)")["errors"])

    def test_coverage_rejects_partial_replay_failure_and_forgery_shapes(self):
        inventory = [{"module": "Solidity.A", "path": "Solidity/A.lean"}]
        good = parser.parse("ℹ [1/1] Built Solidity.A (300s)")
        self.assertEqual([], parser.coverage(inventory, good, 0))
        self.assertTrue(parser.coverage(inventory, parser.parse("✔ [1/1] Built Solidity.A (300.00000000000001s)"), 0))
        self.assertTrue(parser.coverage(inventory, parser.parse("✔ [1/1] Built Solidity.A (300000.00000000000001ms)"), 0))
        self.assertTrue(parser.coverage(inventory, parser.parse("✔ [1/1] Built Solidity.A (0ms)"), 0))
        tampered = parser.parse("✔ [1/1] Built Solidity.A (1s)")
        tampered["rows"][0]["seconds"] = 0.5
        self.assertTrue(parser.coverage(inventory, tampered, 0))
        for log in ["", "✖ [1/1] Built Solidity.A (1s)", "✔ [1/1] Replayed Solidity.A (1s)",
                    "✔ [1/1] Replayed Solidity.A", "✔ [1/1] Built Solidity.A (300.1s)",
                    "✔ [1/1] Built Solidity.A (x)",
                    "✔ [1/1] Built Solidity.A (1s)\n✔ [1/1] Built Solidity.A (1s)",
                    "✔ [1/1] Built Solidity.B (1s)"]:
            with self.subTest(log=log):
                self.assertTrue(parser.coverage(inventory, parser.parse(log), 0))
        self.assertTrue(parser.coverage(inventory, good, 124))
        self.assertTrue(parser.coverage(inventory + inventory, good, 0))
        self.assertTrue(parser.coverage([], good, 0))
        apostrophe = "Loom.DoNames" + chr(39)
        self.assertEqual([], parser.coverage([{"module": apostrophe, "path": "Bridge/vendor/Loom/DoNames" + chr(39) + ".lean"}], parser.parse("✔ [1/1] Built " + apostrophe + " (1s)"), 0))
        self.assertTrue(parser.coverage([{"module": "Solidity.A", "path": "../A.lean"}], good, 0))
        self.assertTrue(parser.coverage([{"module": "A..B", "path": "A.lean"}], good, 0))

if __name__ == "__main__":
    unittest.main()
