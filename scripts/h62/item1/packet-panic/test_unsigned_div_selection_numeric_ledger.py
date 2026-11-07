import hashlib
import json
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
SCRIPT = pathlib.Path(__file__).with_name("unsigned_div_selection_numeric_ledger.py")
SOURCE = "Solidity/Backend/PrimitivePackets/UnsignedDiv/Selection.lean"
CENSUS = pathlib.Path(__file__).with_name("declarations.py")

class LedgerTest(unittest.TestCase):
    def test_source_and_census_controls(self):
        with tempfile.TemporaryDirectory() as d:
            tmp = pathlib.Path(d)
            census = tmp / "census.json"
            census.write_text(subprocess.check_output(["python3", str(CENSUS)], cwd=ROOT, text=True))
            def run(root=ROOT):
                return subprocess.run(["python3", str(SCRIPT), "--root", str(root), "--base-repository", str(ROOT), "--declarations", str(census)], capture_output=True, text=True)
            good = run()
            self.assertEqual(good.returncode, 0, good.stderr)
            self.assertEqual(len(json.loads(good.stdout)["declarations"]), 11)
            original = json.loads(census.read_text())
            source_rows = [r for r in original["declarations"] if r["file"] == SOURCE]
            index = original["declarations"].index(source_rows[0])
            removed = original["declarations"].pop(index)
            census.write_text(json.dumps(original))
            self.assertNotEqual(run().returncode, 0)
            original["declarations"].insert(index, removed)
            original["declarations"].insert(index + 1, dict(removed))
            census.write_text(json.dumps(original))
            self.assertNotEqual(run().returncode, 0)
            original["declarations"].pop(index + 1)
            # Restore original ordering before testing a forged name.
            original = json.loads(subprocess.check_output(["python3", str(CENSUS)], cwd=ROOT, text=True))
            source_rows = [r for r in original["declarations"] if r["file"] == SOURCE]
            source_rows[0]["name"] = "forged"
            census.write_text(json.dumps(original))
            self.assertNotEqual(run().returncode, 0)
            source_rows[0]["name"] = "selectedDiv"
            for field, value in (("line", -1), ("kind", "forged")):
                old = source_rows[0][field]
                source_rows[0][field] = value
                census.write_text(json.dumps(original))
                self.assertNotEqual(run().returncode, 0)
                source_rows[0][field] = old
            census.write_text(json.dumps(original))
            other = "Solidity/Backend/PrimitivePackets/UnsignedDiv/Numeric.lean"
            other_dest = tmp / other
            other_dest.parent.mkdir(parents=True, exist_ok=True)
            other_dest.write_bytes((ROOT / other).read_bytes())
            dest = tmp / SOURCE
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes((ROOT / SOURCE).read_bytes() + b"\n")
            changed_hash = hashlib.sha256(dest.read_bytes()).hexdigest()
            for row in source_rows:
                row["sha256"] = changed_hash
            census.write_text(json.dumps(original))
            self.assertNotEqual(run(tmp).returncode, 0)
            dest.write_bytes((ROOT / SOURCE).read_bytes())
            for row in source_rows:
                row["sha256"] = hashlib.sha256(dest.read_bytes()).hexdigest()
            other_dest.write_bytes(other_dest.read_bytes() + b"\n")
            for row in original["declarations"]:
                if row["file"] == other:
                    row["sha256"] = hashlib.sha256(other_dest.read_bytes()).hexdigest()
            census.write_text(json.dumps(original))
            self.assertNotEqual(run(tmp).returncode, 0)

if __name__ == "__main__": unittest.main()
