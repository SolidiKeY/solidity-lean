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

class SignedLedgerTest(unittest.TestCase):
    def test_reconciliation_and_negative_controls(self):
        declarations = json.loads(subprocess.check_output(["python3", str(DIRECTORY / "declarations.py"), "--root", str(ROOT)]))
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "declarations.json"
            cmd = ["python3", str(DIRECTORY / "signed_controls_ledger.py"), "--root", str(ROOT), "--declarations", str(path)]
            def run(data):
                path.write_text(json.dumps(data))
                return subprocess.run(cmd, capture_output=True, text=True)
            good = run(declarations)
            self.assertEqual(good.returncode, 0, good.stderr)
            result = json.loads(good.stdout)["declarations"]
            self.assertEqual(collections.Counter(r["file"].split("/")[-2] for r in result),
                             {"SignedCheckedAdd": 11, "SignedCheckedSub": 21, "SignedCheckedMul": 39})
            rows = declarations["declarations"]
            index = next(i for i, r in enumerate(rows) if r["file"].endswith("SignedCheckedAdd/Controls.lean"))
            self.assertNotEqual(run({"declarations": rows[:index] + rows[index+1:]}).returncode, 0)
            self.assertNotEqual(run({"declarations": rows + [rows[index]]}).returncode, 0)
            for field, value in (("sha256", "0"*64), ("line", rows[index]["line"]+1), ("kind", "lemma")):
                changed = [dict(row) for row in rows]
                changed[index][field] = value
                self.assertNotEqual(run({"declarations": changed}).returncode, 0)
            copy_root = pathlib.Path(tmp) / "copy"
            for family in ("SignedCheckedAdd", "SignedCheckedSub", "SignedCheckedMul"):
                rel = pathlib.Path("Solidity/Backend/PrimitivePackets") / family / "Controls.lean"
                (copy_root / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / rel, copy_root / rel)
            add = copy_root / rows[index]["file"]
            original = add.read_bytes()
            modified = original.replace(b"by decide", b"by changed", 1)
            self.assertNotEqual(original, modified)
            add.write_bytes(modified)
            changed = [dict(row) for row in rows]
            digest = hashlib.sha256(modified).hexdigest()
            for row in changed:
                if row["file"] == rows[index]["file"]:
                    row["sha256"] = digest
            path.write_text(json.dumps({"declarations": changed}))
            other = ["python3", str(DIRECTORY / "signed_controls_ledger.py"), "--root", str(copy_root), "--declarations", str(path)]
            self.assertNotEqual(subprocess.run(other, capture_output=True).returncode, 0)

if __name__ == "__main__":
    unittest.main()
