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

if __name__ == "__main__":
    unittest.main()
