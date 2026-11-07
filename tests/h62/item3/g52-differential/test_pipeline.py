"""Controls for accounting: synthetic observations never enter external result counts."""
import importlib.util
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[4] / "scripts/h62/item3/g52-differential/pipeline.py"
spec = importlib.util.spec_from_file_location("pipeline", SCRIPT)
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)

class Accounting(unittest.TestCase):
    def row(self):
        return dict(status="executed", fork="Osaka", halt="return", output="0x", storage={"0": "7"}, storage_full={}, logs=[], rollback=True)

    def test_skip_is_not_match(self):
        self.assertEqual(p.compare(dict(status="unsupported"), self.row())["status"], "unsupported")
        self.assertEqual(p.compare({}, {})["status"], "unsupported")

    def test_missing_observation_is_error(self):
        row = self.row()
        del row["logs"]
        with self.assertRaises(ValueError): p.compare(row, self.row())

    def test_each_observation_has_negative_control(self):
        for field, value in [("halt", "revert"), ("output", "0x01"), ("storage", {"0": "8"}),
                             ("storage_full", {"0x" + "00" * 32: "0x08"}), ("logs", [dict(address="0x" + "00" * 20, topics=[], data="0x")]), ("rollback", False)]:
            row = self.row(); row[field] = value
            self.assertEqual(p.compare(row, self.row())["fields"], [field])

    def test_gas_needs_same_metric(self):
        a = self.row(); b = self.row()
        a.update(gas_metric="message", gas_used="10")
        self.assertEqual(p.compare(a, b)["gas_status"], "unsupported")
        b.update(gas_metric="transaction", gas_used="11")
        self.assertEqual(p.compare(a, b)["gas_status"], "unsupported")
        b["gas_metric"] = "message"
        self.assertEqual(p.compare(a, b)["fields"], ["gas_used"])

    def test_wrong_fork_is_unsupported(self):
        row = self.row(); row["fork"] = "Cancun"
        self.assertEqual(p.compare(row, self.row())["status"], "unsupported")

    def test_invalid_results_cannot_match(self):
        for updates in [dict(storage={"garbage": None}), dict(logs=[None])]:
            row = self.row(); row.update(updates)
            with self.assertRaises(ValueError): p.compare(row, row)
        row = self.row(); row["rollback"] = False
        self.assertEqual(p.compare(row, row)["status"], "mismatch")

    def test_inputs_are_unique(self):
        import json
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); p.generate(root)
            cases = json.loads((root/"generated/cases.json").read_text())["cases"]
            self.assertEqual(len(cases), len({(c["source"], c["x"]) for c in cases}))

    def test_empty_case_manifest_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            p.write(root/"generated/cases.json", dict(cases=[]))
            with self.assertRaises(ValueError): p.compare_results(root)

    def test_provenance_and_stale_results_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            p.write(root/"upstream/fixtures_develop-v5.3.0.tar.gz", {})
            with self.assertRaisesRegex(ValueError, "checksum"):
                p.census(root)
            p.write(root/"evidence/stale.json", dict(input_sha256="wrong"))
            p.write(root/"generated/cases.json", {})
            with self.assertRaisesRegex(ValueError, "bind current"):
                p.load_results(root/"evidence/stale.json", root, "semantics")

    def test_generator_reproduces(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b:
            self.assertEqual(p.generate(Path(a)), p.generate(Path(b)))
            self.assertEqual((Path(a)/"generated/cases.json").read_bytes(), (Path(b)/"generated/cases.json").read_bytes())

if __name__ == "__main__": unittest.main()
