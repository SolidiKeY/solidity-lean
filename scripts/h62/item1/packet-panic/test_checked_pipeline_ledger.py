#!/usr/bin/env python3
import collections
import hashlib
import json
import pathlib
import shutil
import subprocess
import tempfile
import unittest

DIRECTORY = pathlib.Path(__file__).resolve().parent
ROOT = DIRECTORY.parents[3]

class CheckedPipelineLedgerTest(unittest.TestCase):
    def test_base_pinning_and_census_reconciliation(self):
        declarations = json.loads(subprocess.check_output(["python3", str(DIRECTORY / "declarations.py"), "--root", str(ROOT)]))
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "declarations.json"
            cmd = ["python3", str(DIRECTORY / "checked_pipeline_ledger.py"), "--root", str(ROOT), "--declarations", str(path)]
            def run(data):
                path.write_text(json.dumps(data))
                return subprocess.run(cmd, capture_output=True, text=True)
            good = run(declarations)
            self.assertEqual(good.returncode, 0, good.stderr)
            result = json.loads(good.stdout)["declarations"]
            self.assertEqual(len(result), 89)
            self.assertEqual(collections.Counter(r["file"].split("/")[-2] for r in result),
                             {"CheckedAdd": 14, "CheckedSub": 17, "CheckedMul": 16,
                              "SignedCheckedAdd": 13, "SignedCheckedSub": 14, "SignedCheckedMul": 15})
            rows = declarations["declarations"]
            index = next(i for i, r in enumerate(rows) if r["file"].endswith("CheckedAdd/Source.lean"))
            self.assertNotEqual(run({"declarations": rows[:index]+rows[index+1:]}).returncode, 0)
            self.assertNotEqual(run({"declarations": rows+[rows[index]]}).returncode, 0)
            for field, value in (("sha256", "0"*64), ("line", rows[index]["line"]+1), ("kind", "lemma")):
                changed = [dict(row) for row in rows]
                changed[index][field] = value
                self.assertNotEqual(run({"declarations": changed}).returncode, 0)
            copy_root = pathlib.Path(tmp) / "copy"
            families = ("CheckedAdd", "CheckedSub", "CheckedMul", "SignedCheckedAdd", "SignedCheckedSub", "SignedCheckedMul")
            for family in families:
                for name in ("Source.lean", "Selected.lean", "Target.lean", "Agreement.lean"):
                    rel = pathlib.Path("Solidity/Backend/PrimitivePackets") / family / name
                    (copy_root / rel).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(ROOT / rel, copy_root / rel)
            target = copy_root / rows[index]["file"]
            original = target.read_bytes()
            changed_bytes = original.replace(b"by", b"by_changed", 1)
            self.assertNotEqual(changed_bytes, original)
            target.write_bytes(changed_bytes)
            changed = [dict(row) for row in rows]
            for row in changed:
                if row["file"] == rows[index]["file"]:
                    row["sha256"] = hashlib.sha256(changed_bytes).hexdigest()
            path.write_text(json.dumps({"declarations": changed}))
            other = ["python3", str(DIRECTORY / "checked_pipeline_ledger.py"), "--root", str(copy_root), "--base-repository", str(ROOT), "--declarations", str(path)]
            failure = subprocess.run(other, capture_output=True, text=True)
            self.assertNotEqual(failure.returncode, 0)
            self.assertIn("source bytes differ", failure.stderr)

if __name__ == "__main__":
    unittest.main()
