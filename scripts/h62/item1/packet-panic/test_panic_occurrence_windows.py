import hashlib
import importlib.util
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("panic_occurrence_windows", pathlib.Path(__file__).with_name("panic_occurrence_windows.py"))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class OccurrenceWindowsTest(unittest.TestCase):
    def test_multiple_tokens_unmapped_and_ambiguous(self):
        rows = module.occurrences("x.lean", b"-- panicData panicData2 panicData\n")
        self.assertEqual([(r["line"], r["column"]) for r in rows], [(1, 4), (1, 25)])
        # Raw word-boundary regex also matches an apostrophe identifier suffix.
        self.assertEqual(len(module.occurrences("x.lean", b"panicData'")), 1)
        self.assertEqual(module.occurrences("x.lean", "λ panicData".encode())[0]["column"], 3)
        sample = b"Source.panicData -- panicData\n/- outer /- panicData -/ -/\n\"panicData\"\n@[x panicData] panicData'\nfoo'panicData\n"
        self.assertEqual([r["lexical_candidate"] for r in module.occurrences("x.lean", sample)],
                         [True, False, False, False, False, False, False])
        w = {"file": "x.lean", "source_sha256": rows[0]["source_sha256"], "line": 1, "end_line": 1, "kind": "theorem", "name": "x", "ledger": "l", "window_sha256": "h"}
        self.assertEqual(len(module.link(rows, [w])), 2)
        self.assertIsNone(module.link(rows, [])[0]["window"])
        with self.assertRaises(ValueError): module.link(rows, [w, dict(w)])
        with self.assertRaises(ValueError): module.link(rows, [dict(w, source_sha256="wrong")])

    def test_registered_helper_snapshot_and_header_controls(self):
        root = pathlib.Path(__file__).resolve().parents[4]
        data = (root / module.HELPER_PATH).read_bytes()
        with tempfile.TemporaryDirectory() as tmp:
            fake_root = pathlib.Path(tmp)
            helper = fake_root / module.HELPER_PATH
            helper.parent.mkdir(parents=True)
            helper.write_bytes(data)
            with patch.object(module.subprocess, "check_output", return_value=data):
                windows = module.canonical_helper_windows(fake_root)
                self.assertEqual([w["name"] for w in windows], list(module.HELPER_NAMES))
                helper.write_bytes(data + b"\n")
                with self.assertRaisesRegex(ValueError, "differs from registered"):
                    module.canonical_helper_windows(fake_root)
            malformed = data.replace(b"theorem panic_not_empty", b"theorem renamed", 1)
            helper.write_bytes(malformed)
            with patch.object(module.subprocess, "check_output", return_value=malformed):
                with self.assertRaisesRegex(ValueError, "headers differ"):
                    module.canonical_helper_windows(fake_root)

    def test_cli_emits_zero_and_unmapped_results_before_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            path = root / "Solidity/Backend/PrimitivePackets/X/Test.lean"
            path.parent.mkdir(parents=True)
            relative = path.relative_to(root).as_posix()
            def run(data, windows):
                path.write_bytes(data)
                payload = json.dumps({"windows": windows}).encode()
                script = pathlib.Path(module.__file__).resolve()
                wrapper = ("import importlib.util,subprocess,sys; "
                           + "sys.path.insert(0," + repr(str(script.parent)) + "); "
                           + "spec=importlib.util.spec_from_file_location('scan'," + repr(str(script)) + "); "
                           + "m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m); "
                           + "m.canonical_helper_windows=lambda root: []; "
                           + "m.subprocess.check_output=lambda *a,**k: " + repr(payload) + "; "
                           + "sys.argv=[" + repr(str(script)) + ", '--declarations', 'ignored']; "
                           + "raise SystemExit(m.main())")
                result = subprocess.run([sys.executable, "-B", "-c", wrapper], cwd=root, capture_output=True, text=True)
                return result, json.loads(result.stdout)
            zero, zero_json = run(b"no hits\n", [])
            self.assertEqual((zero.returncode, zero_json["occurrences"], zero_json["unmapped"]), (2, 0, 0))
            unmapped, unmapped_json = run(b"panicData\n", [])
            self.assertEqual((unmapped.returncode, unmapped_json["occurrences"], unmapped_json["unmapped"]), (3, 1, 1))
            self.assertIsNone(unmapped_json["rows"][0]["window"])
            digest = hashlib.sha256(b"panicData\n").hexdigest()
            window = {"file": relative, "source_sha256": digest, "line": 1, "end_line": 1, "kind": "theorem", "name": "x", "ledger": "l", "window_sha256": "h"}
            good, good_json = run(b"panicData\n", [window])
            self.assertEqual((good.returncode, good_json["occurrences"], good_json["unmapped"]), (0, 1, 0))

if __name__ == "__main__": unittest.main()
