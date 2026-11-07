"""Guard relocation against changed/missing historical bytes and prefix escape.

Fixtures are synthetic checksum inputs only, never Lean or formal-proof evidence.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[3] / "h28-sol/automation-benchmark/h82-static-handoff-v1/verify.py"
spec = importlib.util.spec_from_file_location("h28_packet_verifier", SCRIPT)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


class PacketRelocationControls(unittest.TestCase):
    def fixture(self, root):
        entries = []
        for i in range(20):
            payload = f"synthetic checksum input {i}\n".encode()
            (root / str(i)).write_bytes(payload)
            entries.append({"path": f"/historical/{i}", "bytes": len(payload),
                            "sha256": hashlib.sha256(payload).hexdigest()})
        return entries

    def test_complete_relocation_and_original_manifest_unchanged(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); entries = self.fixture(root); before = json.dumps(entries)
            verifier.verify_entries(entries, verifier.path_maps([("/historical", str(root))]))
            self.assertEqual(json.dumps(entries), before)

    def test_same_size_tampering_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); entries = self.fixture(root)
            p = root / "19"; p.write_bytes(b"X" * p.stat().st_size)
            with self.assertRaisesRegex(ValueError, "SHA256"):
                verifier.verify_entries(entries, verifier.path_maps([("/historical", str(root))]))

    def test_missing_mapped_file_has_no_original_path_fallback(self):
        with tempfile.TemporaryDirectory() as old, tempfile.TemporaryDirectory() as new:
            root = Path(old); entries = self.fixture(root)
            for entry in entries: entry["path"] = str(root / Path(entry["path"]).name)
            with self.assertRaises(FileNotFoundError):
                verifier.verify_entries(entries, verifier.path_maps([(old, new)]))

    def test_longest_component_prefix_and_no_sibling_match(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b:
            maps = verifier.path_maps([("/historical", a), ("/historical/nested", b)])
            self.assertEqual(verifier.source_path("/historical/nested/file", maps), Path(b) / "file")
            self.assertEqual(verifier.source_path("/historical-sibling/file", maps), Path("/historical-sibling/file"))

    def test_duplicate_relative_and_parent_roots_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            for pairs in [[("/old", temp), ("/old", temp)], [("relative", temp)],
                          [("/old/../other", temp)], [("/old", "relative")]]:
                with self.subTest(pairs=pairs), self.assertRaises(ValueError):
                    verifier.path_maps(pairs)
            with self.assertRaises(ValueError): verifier.source_path("/old/../file", [])

    def test_symlink_escape_refused(self):
        with tempfile.TemporaryDirectory() as root, tempfile.TemporaryDirectory() as outside:
            (Path(root) / "escape").symlink_to(outside, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "escapes"):
                verifier.source_path("/old/escape/file", verifier.path_maps([("/old", root)]))

    def test_full_entry_count_required(self):
        with self.assertRaisesRegex(ValueError, "exactly 20"):
            verifier.verify_entries([])

    def test_optimized_python_still_refuses_wrong_bytes(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); entries = self.fixture(root)
            entries[0]["sha256"] = "0" * 64
            manifest = root / "entries.json"; manifest.write_text(json.dumps(entries))
            code = ("import importlib.util,json,sys; "
                    "s=importlib.util.spec_from_file_location('v',sys.argv[1]); "
                    "m=importlib.util.module_from_spec(s); s.loader.exec_module(m); "
                    "m.verify_entries(json.load(open(sys.argv[2])),m.path_maps([('/historical',sys.argv[3])]))")
            p = subprocess.run([sys.executable, "-O", "-c", code, str(SCRIPT), str(manifest), temp],
                               capture_output=True, text=True)
            self.assertNotEqual(p.returncode, 0)
            self.assertIn("SHA256 mismatch", p.stderr)


if __name__ == "__main__":
    unittest.main()
