#!/usr/bin/env python3
import json
import pathlib
import hashlib
import shutil
import subprocess
import tempfile
import unittest

DIRECTORY = pathlib.Path(__file__).resolve().parent
ROOT = DIRECTORY.parents[3]


class LedgerTest(unittest.TestCase):
    def test_reconciliation_and_negative_controls(self):
        declarations = json.loads(subprocess.check_output(
            ["python3", str(DIRECTORY / "declarations.py"), "--root", str(ROOT)]))
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "declarations.json"
            cmd = ["python3", str(DIRECTORY / "controls_ledger.py"), "--root", str(ROOT), "--declarations", str(path)]
            def run(data):
                path.write_text(json.dumps(data))
                return subprocess.run(cmd, capture_output=True, text=True)
            good = run(declarations)
            self.assertEqual(good.returncode, 0, good.stderr)
            self.assertEqual(len(json.loads(good.stdout)["declarations"]), 102)
            rows = declarations["declarations"]
            index = next(i for i, r in enumerate(rows) if r["file"].endswith("CheckedAdd/Controls.lean"))
            missing = {"declarations": rows[:index] + rows[index + 1:]}
            self.assertNotEqual(run(missing).returncode, 0)
            duplicate = {"declarations": rows + [rows[index]]}
            self.assertNotEqual(run(duplicate).returncode, 0)
            changed = [dict(row) for row in rows]
            changed[index]["sha256"] = "0" * 64
            self.assertNotEqual(run({"declarations": changed}).returncode, 0)
            for field, value in (("line", rows[index]["line"] + 1), ("kind", "lemma")):
                changed = [dict(row) for row in rows]
                changed[index][field] = value
                self.assertNotEqual(run({"declarations": changed}).returncode, 0)
            copy_root = pathlib.Path(tmp) / "copy"
            for family in ("CheckedAdd", "CheckedSub", "CheckedMul"):
                rel = pathlib.Path("Solidity/Backend/PrimitivePackets") / family / "Controls.lean"
                (copy_root / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / rel, copy_root / rel)
            add = copy_root / rows[index]["file"]
            original = add.read_bytes()
            modified = original.replace(b"exact result", b"exact changed", 1)
            self.assertNotEqual(original, modified)
            add.write_bytes(modified)
            changed = [dict(row) for row in rows]
            new_hash = hashlib.sha256(add.read_bytes()).hexdigest()
            for row in changed:
                if row["file"] == rows[index]["file"]:
                    row["sha256"] = new_hash
            path.write_text(json.dumps({"declarations": changed}))
            changed_cmd = ["python3", str(DIRECTORY / "controls_ledger.py"), "--root", str(copy_root), "--declarations", str(path)]
            self.assertNotEqual(subprocess.run(changed_cmd, capture_output=True).returncode, 0)


if __name__ == "__main__":
    unittest.main()
