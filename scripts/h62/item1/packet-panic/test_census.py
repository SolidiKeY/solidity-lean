#!/usr/bin/env python3
import json
import pathlib
import subprocess
import tempfile
import unittest

SCRIPT = pathlib.Path(__file__).with_name("census.py")

class CensusTest(unittest.TestCase):
    def test_fixture_and_missing_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            registry = root / "owners.json"
            registry.write_text(json.dumps({"masterHead": "fixture", "items": [
                {"id": "G25-test", "owner": "fixture", "status": "assigned",
                 "writeScope": "Solidity/Backend/PrimitivePackets/A/**"}]}))
            cmd = ["python3", str(SCRIPT), "--root", str(root), "--ownership", str(registry)]
            self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
            directory = root / "Solidity/Backend/PrimitivePackets/A"
            directory.mkdir(parents=True)
            (directory / "Controls.lean").write_text("\n-- theorem exact_panic_bytes : False\n\ntheorem exact_panic_bytes : True := by trivial\n\ntheorem exact_panic : True := by trivial\n")
            result = json.loads(subprocess.check_output(cmd))
            self.assertEqual([(x["line"], x["declaration"]) for x in result["declarations"]],
                             [(4, "exact_panic_bytes"), (6, "exact_panic")])
            self.assertEqual(result["declarations"][0]["g25_reservations"][0]["id"], "G25-test")


    def test_nested_comments_strings_and_formatting(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            registry = root / "owners.json"
            registry.write_text(json.dumps({"items": []}))
            directory = root / "Solidity/Backend/PrimitivePackets/A"
            directory.mkdir(parents=True)
            fixture = directory / "Controls.lean"
            fixture.write_text(
                "/- outer\n/- theorem exact_panic : False -/\ntheorem panic_not_empty : False\n-/\n"
                "def s := \"theorem exact_panic_bytes -- /-\"\n"
                "def c : Char := '\"'\n"
                "theorem exact_panic' : True := by trivial\n"
                "theorem exact_panic.foo : True := by trivial\n"
                "@[simp, foo [bar], foo /- ] -/, bar \" ] \"] @[other] private theorem\n  exact_panic_bytes : True := by trivial\n"
                "protected theorem panic_not_truncated : True := by trivial\n")
            cmd = ["python3", str(SCRIPT), "--root", str(root), "--ownership", str(registry)]
            result = json.loads(subprocess.check_output(cmd))
            self.assertEqual([(x["line"], x["declaration"]) for x in result["declarations"]],
                             [(10, "exact_panic_bytes"), (11, "panic_not_truncated")])
            fixture.write_text("/- unterminated")
            failed = subprocess.run(cmd, capture_output=True, text=True)
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn("unterminated", failed.stderr)

if __name__ == "__main__":
    unittest.main()
