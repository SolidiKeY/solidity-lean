import importlib.util
import json
import subprocess
import sys
import tempfile
import pathlib
import unittest

spec = importlib.util.spec_from_file_location("ledger_totals", pathlib.Path(__file__).with_name("ledger_totals.py"))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

def row(name, line):
    return {"file": "test.lean", "line": line, "kind": "theorem", "name": name, "sha256": "hash"}

class LedgerTotalsTest(unittest.TestCase):
    def test_disjoint_and_negative_controls(self):
        a, b, c, private = row("a", 1), row("b", 2), row("c", 3), row("p", 4)
        result = module.summarize([a, b, c], [("one", [a]), ("two", [b]), (module.PRIVATE, [private])])
        self.assertEqual((result["observed_headers"], result["described_total"], result["unclassified_original"]), (4, 3, 1))
        self.assertEqual(result["unclassified"], [c])
        module.validate_census([a, b], [a, b])
        for supplied in ([a], [a, b, c], [b, a]):
            with self.assertRaises(ValueError): module.validate_census(supplied, [a, b])
        for census, ledgers in (
            ([a, a], [("one", [a])]),
            ([a, b], [("one", [a]), ("two", [a])]),
            ([a], [("one", [b])]),
            ([a], [(module.PRIVATE, [a])]),
            ([a], [("one", [a]), ("one", [])]),
        ):
            with self.assertRaises(ValueError): module.summarize(census, ledgers)

    def test_cli_rejects_forged_unclassified_census(self):
        directory = pathlib.Path(__file__).resolve().parent
        root = directory.parents[3]
        rows = json.loads(subprocess.check_output([sys.executable, str(directory / "declarations.py")], cwd=root))["declarations"]
        index = next(i for i, r in enumerate(rows) if r["file"].endswith("SignedSub/Controls.lean"))
        forged = dict(rows[index], name="invented_header")
        with tempfile.TemporaryDirectory() as tmp:
            census = pathlib.Path(tmp) / "census.json"
            for changed in (rows[:index] + rows[index+1:], rows + [forged]):
                census.write_text(json.dumps({"declarations": changed}))
                result = subprocess.run([sys.executable, str(directory / "ledger_totals.py"), "--declarations", str(census)], cwd=root, capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("supplied census differs", result.stderr)

if __name__ == "__main__": unittest.main()
