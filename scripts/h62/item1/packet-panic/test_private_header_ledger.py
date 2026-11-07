import hashlib
import json
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
SCRIPT = pathlib.Path(__file__).with_name("private_header_ledger.py")
CENSUS = pathlib.Path(__file__).with_name("declarations.py")

class PrivateHeaderLedgerTest(unittest.TestCase):
    def test_pinned_census_and_changed_source(self):
        with tempfile.TemporaryDirectory() as d:
            tmp = pathlib.Path(d)
            census = tmp / "census.json"
            original = json.loads(subprocess.check_output(["python3", str(CENSUS)], cwd=ROOT, text=True))
            census.write_text(json.dumps(original))
            def run(root):
                return subprocess.run(["python3", str(SCRIPT), "--root", str(root), "--base-repository", str(ROOT), "--declarations", str(census)], capture_output=True, text=True)
            good = run(ROOT)
            self.assertEqual(good.returncode, 0, good.stderr)
            self.assertEqual(len(json.loads(good.stdout)["declarations"]), 9)
            files = {r["file"] for r in original["declarations"]}
            chosen = "Solidity/Backend/PrimitivePackets/UnsignedDiv/SourceOrigin.lean"
            missing = {"declarations": [r for r in original["declarations"] if r["file"] != chosen]}
            census.write_text(json.dumps(missing))
            self.assertNotEqual(run(ROOT).returncode, 0)
            substitute = "Solidity/Backend/PrimitivePackets/Comparisons/Controls.lean"
            replacement = "Solidity/Backend/PrimitivePackets/CheckedAdd/Source.lean"
            substitute_hash = hashlib.sha256((ROOT / substitute).read_bytes()).hexdigest()
            forged = {"declarations": [r for r in original["declarations"] if r["file"] != replacement] + [{"file": substitute, "sha256": substitute_hash, "line": 1, "kind": "def", "name": "fake"}]}
            census.write_text(json.dumps(forged))
            self.assertNotEqual(run(ROOT).returncode, 0)
            census.write_text(json.dumps(original))
            for file in files:
                dest = tmp / file
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes((ROOT / file).read_bytes())
            dest = tmp / chosen
            dest.write_bytes(dest.read_bytes() + b"\nprivate theorem fabricated : True := by trivial\n")
            digest = hashlib.sha256(dest.read_bytes()).hexdigest()
            for row in original["declarations"]:
                if row["file"] == chosen: row["sha256"] = digest
            census.write_text(json.dumps(original))
            self.assertNotEqual(run(tmp).returncode, 0)

if __name__ == "__main__": unittest.main()
