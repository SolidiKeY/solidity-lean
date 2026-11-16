"""Private summary integrity and unavailable controls; no Lean/compatibility claim."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location("private_portable", Path(__file__).with_name("verify-portable-evidence-v2.py"))
v2 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(v2)
BASE = "c7f33cfc9e1b3c8d0e634f0b267971aa2671688d"


class PrivatePortableTests(unittest.TestCase):
    def setUp(self):
        directory = Path(tempfile.gettempdir()).resolve()
        if directory.is_relative_to(ROOT):
            directory = ROOT.parent
        self.temp = tempfile.TemporaryDirectory(dir=directory)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name in v2.PINS:
            raw = subprocess.check_output(["git", "--no-replace-objects", "show", BASE + ":" + name], cwd=ROOT)
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)

    def test_private_inputs_without_repository_reads(self):
        old_open = Path.open
        def guarded_open(path, *args, **kwargs):
            if any(path.resolve() == ROOT / name for name in v2.PINS):
                raise AssertionError("repository summary read forbidden")
            return old_open(path, *args, **kwargs)
        with patch.object(Path, "open", guarded_open):
            report = v2.verify(self.root)
        self.assertEqual(report["historical_summaries"], "verified")
        self.assertEqual(report["repository_support_files"], "verified")
        self.assertNotIn("repository_summaries", report)
        self.assertEqual([r["status"] for r in report["bulk"]], ["unavailable", "unavailable"])
        self.assertIs(report["compatibility_accepted"], False)
        self.assertIs(report["lean_run"], False)

    def test_same_size_corruption_refused(self):
        path = self.root / next(iter(v2.PINS))
        raw = path.read_bytes()
        path.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
        with self.assertRaisesRegex(ValueError, "Historical summary checksum mismatch"):
            v2.verify(self.root)

    def test_missing_private_summary_has_no_fallback(self):
        (self.root / next(iter(v2.PINS))).unlink()
        with self.assertRaises(FileNotFoundError):
            v2.verify(self.root)

    def test_catalog_cannot_repin_private_input(self):
        catalog = copy.deepcopy(v2.legacy.load_catalog())
        catalog["repository_files"][0]["sha256"] = "0" * 64
        with patch.object(v2.legacy, "load_catalog", return_value=catalog):
            with self.assertRaisesRegex(ValueError, "catalog checksum mismatch"):
                v2.verify(self.root)

    def test_catalog_cannot_omit_or_duplicate_summaries(self):
        original = v2.legacy.load_catalog()
        for rows in (original["repository_files"][1:], [original["repository_files"][0]] * 2 + original["repository_files"][2:]):
            catalog = copy.deepcopy(original)
            catalog["repository_files"] = rows
            with self.subTest(rows=rows), patch.object(v2.legacy, "load_catalog", return_value=catalog):
                with self.assertRaisesRegex(ValueError, "catalog membership mismatch"):
                    v2.verify(self.root)

    def test_remaining_repository_checks_preserved(self):
        with patch.object(v2.legacy, "repository_digest", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "Repository checksum mismatch"):
                v2.verify(self.root)

    def test_corrupt_bulk_is_failure(self):
        artifacts = self.root / "artifacts"
        artifacts.mkdir()
        (artifacts / "original-evidence.tar.gz").write_bytes(b"corrupt archive")
        with self.assertRaisesRegex(ValueError, "Archive checksum mismatch"):
            v2.verify(self.root, artifacts)

    def test_require_bulk_stays_nonzero_and_unavailable(self):
        run = subprocess.run([sys.executable, "-B", str(Path(v2.__file__)),
                              "--historical-input-root", str(self.root), "--require-bulk"],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 1, run.stderr)
        report = json.loads(run.stdout)
        self.assertEqual([r["status"] for r in report["bulk"]], ["unavailable", "unavailable"])
        self.assertIs(report["compatibility_accepted"], False)
        self.assertIs(report["lean_run"], False)

    def test_repository_and_symlink_escape_refused(self):
        with self.assertRaisesRegex(ValueError, "outside the repository"):
            v2.verify(ROOT)
        nested = self.root / "nested"
        for name in v2.PINS:
            path = nested / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.symlink_to(self.root / name)
        with self.assertRaisesRegex(ValueError, "escapes"):
            v2.verify(nested)


if __name__ == "__main__":
    unittest.main()
