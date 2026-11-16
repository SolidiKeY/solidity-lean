"""Guard H145 private evidence relocation from admission repinning or data loss."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock
spec=importlib.util.spec_from_file_location('private_evidence_controls',Path(__file__).with_name('primitive_read_coverage.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class PrivateEvidenceControls(unittest.TestCase):
    def test_same_buffer_digest_and_pair(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'admission.json';pins={'frozen':'f'*64,'current':'c'*64};raw=json.dumps(pins).encode();path.write_bytes(raw)
            with mock.patch.object(m,'ADMISSION_SHA256',m.gate.hashlib.sha256(raw).hexdigest()):
                actual,digest,pair=m.read_admission(path);self.assertEqual(actual,path.resolve());self.assertEqual(pair,pins)
                path.write_bytes(raw+b' ')
                with self.assertRaisesRegex(ValueError,'unadmitted'):m.read_admission(path)
    def test_public_checkout_admission_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);path=root/'admission.json';path.write_text('{}')
            with mock.patch.object(m.gate,'ROOT',root):
                with self.assertRaisesRegex(ValueError,'outside public'):m.read_admission(path)
    def test_incomplete_mode_pair_refused_even_if_digest_matches(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'admission.json';raw=b'{"frozen":"wrong"}';path.write_bytes(raw)
            with mock.patch.object(m,'ADMISSION_SHA256',m.gate.hashlib.sha256(raw).hexdigest()):
                with self.assertRaisesRegex(ValueError,'incomplete'):m.read_admission(path)
    def test_public_output_refused_before_creation(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);path=root/'tests/receipts'
            with mock.patch.object(m.gate,'ROOT',root):
                with self.assertRaisesRegex(ValueError,'outside public'):m.prepare_output(path)
            self.assertFalse(path.exists())
    def test_output_never_overwrites_existing_data(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'out';m.prepare_output(path);saved=path/'keep';saved.write_text('retained')
            with self.assertRaises(FileExistsError):m.prepare_output(path)
            self.assertEqual(saved.read_text(),'retained')



# Historical report readers share the private relocation/integrity boundary.
import copy
import subprocess
import sys
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[4]
BASE = "c7f33cfc9e1b3c8d0e634f0b267971aa2671688d"

def load_reader(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

language_reader = load_reader("private_language_export", "scripts/h62/item2/audit-language/export.py")
portable_reader = load_reader("private_portable", "scripts/h62/item6/migrate-solkey/verify-portable-evidence.py")

class PrivateExportTests(unittest.TestCase):
    def setUp(self):
        directory = Path(tempfile.gettempdir()).resolve()
        if directory.is_relative_to(ROOT):
            directory = ROOT.parent
        self.temp = tempfile.TemporaryDirectory(dir=directory)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.raw = subprocess.check_output(["git", "--no-replace-objects", "show", BASE + ":" + language_reader.REQUEST], cwd=ROOT)
        self.input = self.root / language_reader.REQUEST
        self.input.parent.mkdir(parents=True)
        self.input.write_bytes(self.raw)

    def test_exact_historical_json(self):
        self.assertEqual(language_reader.load_historical_request(self.root), json.loads(self.raw))

    def test_same_size_corruption_refused(self):
        self.input.write_bytes(bytes([self.raw[0] ^ 1]) + self.raw[1:])
        with self.assertRaisesRegex(ValueError, "checksum mismatch"):
            language_reader.load_historical_request(self.root)

    def test_missing_private_input_has_no_repository_fallback(self):
        self.input.unlink()
        old_open = Path.open
        def guarded_open(path, *args, **kwargs):
            if path.resolve() == ROOT / language_reader.REQUEST:
                raise AssertionError("repository fallback forbidden")
            return old_open(path, *args, **kwargs)
        with patch.object(Path, "open", guarded_open), self.assertRaises(FileNotFoundError):
            language_reader.load_historical_request(self.root)

    def test_repository_input_root_refused(self):
        with self.assertRaisesRegex(ValueError, "outside the repository"):
            language_reader.load_historical_request(ROOT)

    def test_symlink_escape_refused(self):
        outside = self.root / "outside.json"
        outside.write_bytes(self.raw)
        # The declared root is a separate directory; a sibling target escapes it.
        nested = self.root / "nested"
        candidate = nested / language_reader.REQUEST
        candidate.parent.mkdir(parents=True)
        candidate.symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "escapes"):
            language_reader.load_historical_request(nested)

    def test_cli_delegates_only_authenticated_value(self):
        output = self.root / "output"
        argv = ["export.py", "--output", str(output), "--interface-version", "2", "--historical-input-root", str(self.root)]
        with patch.object(sys, "argv", argv), patch.object(language_reader, "export") as exporter:
            language_reader.main()
        exporter.assert_called_once_with(output, owner_request=json.loads(self.raw))
        self.input.write_bytes(self.raw + b" ")
        with patch.object(sys, "argv", argv), patch.object(language_reader, "export") as exporter:
            with self.assertRaisesRegex(ValueError, "checksum mismatch"):
                language_reader.main()
            exporter.assert_not_called()

    def test_original_branch_guard_precedes_output(self):
        output = self.root / "output"
        with patch.object(language_reader, "git", return_value=b"another-branch\n"):
            with self.assertRaises(AssertionError):
                language_reader.export(output, owner_request=json.loads(self.raw))
        self.assertFalse(output.exists())


class PrivatePortableTests(unittest.TestCase):
    def setUp(self):
        directory = Path(tempfile.gettempdir()).resolve()
        if directory.is_relative_to(ROOT):
            directory = ROOT.parent
        self.temp = tempfile.TemporaryDirectory(dir=directory)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name in portable_reader.HISTORICAL_PINS:
            raw = subprocess.check_output(["git", "--no-replace-objects", "show", BASE + ":" + name], cwd=ROOT)
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)

    def test_private_inputs_without_repository_reads(self):
        old_open = Path.open
        def guarded_open(path, *args, **kwargs):
            if any(path.resolve() == ROOT / name for name in portable_reader.HISTORICAL_PINS):
                raise AssertionError("repository summary read forbidden")
            return old_open(path, *args, **kwargs)
        with patch.object(Path, "open", guarded_open):
            report = portable_reader.verify_v2(self.root)
        self.assertEqual(report["historical_summaries"], "verified")
        self.assertEqual(report["repository_support_files"], "verified")
        self.assertNotIn("repository_summaries", report)
        self.assertEqual([r["status"] for r in report["bulk"]], ["unavailable", "unavailable"])
        self.assertIs(report["compatibility_accepted"], False)
        self.assertIs(report["lean_run"], False)

    def test_same_size_corruption_refused(self):
        path = self.root / next(iter(portable_reader.HISTORICAL_PINS))
        raw = path.read_bytes()
        path.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
        with self.assertRaisesRegex(ValueError, "Historical summary checksum mismatch"):
            portable_reader.verify_v2(self.root)

    def test_missing_private_summary_has_no_fallback(self):
        (self.root / next(iter(portable_reader.HISTORICAL_PINS))).unlink()
        with self.assertRaises(FileNotFoundError):
            portable_reader.verify_v2(self.root)

    def test_catalog_cannot_repin_private_input(self):
        catalog = copy.deepcopy(portable_reader.load_catalog())
        catalog["repository_files"][0]["sha256"] = "0" * 64
        with patch.object(portable_reader, "load_catalog", return_value=catalog):
            with self.assertRaisesRegex(ValueError, "catalog checksum mismatch"):
                portable_reader.verify_v2(self.root)

    def test_catalog_cannot_omit_or_duplicate_summaries(self):
        original = portable_reader.load_catalog()
        for rows in (original["repository_files"][1:], [original["repository_files"][0]] * 2 + original["repository_files"][2:]):
            catalog = copy.deepcopy(original)
            catalog["repository_files"] = rows
            with self.subTest(rows=rows), patch.object(portable_reader, "load_catalog", return_value=catalog):
                with self.assertRaisesRegex(ValueError, "catalog membership mismatch"):
                    portable_reader.verify_v2(self.root)

    def test_remaining_repository_checks_preserved(self):
        with patch.object(portable_reader, "repository_digest", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "Repository checksum mismatch"):
                portable_reader.verify_v2(self.root)

    def test_corrupt_bulk_is_failure(self):
        artifacts = self.root / "artifacts"
        artifacts.mkdir()
        (artifacts / "original-evidence.tar.gz").write_bytes(b"corrupt archive")
        with self.assertRaisesRegex(ValueError, "Archive checksum mismatch"):
            portable_reader.verify_v2(self.root, artifacts)

    def test_require_bulk_stays_nonzero_and_unavailable(self):
        run = subprocess.run([sys.executable, "-B", str(Path(portable_reader.__file__)),
                              "--interface-version", "2", "--historical-input-root", str(self.root), "--require-bulk"],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 1, run.stderr)
        report = json.loads(run.stdout)
        self.assertEqual([r["status"] for r in report["bulk"]], ["unavailable", "unavailable"])
        self.assertIs(report["compatibility_accepted"], False)
        self.assertIs(report["lean_run"], False)

    def test_repository_and_symlink_escape_refused(self):
        with self.assertRaisesRegex(ValueError, "outside the repository"):
            portable_reader.verify_v2(ROOT)
        nested = self.root / "nested"
        for name in portable_reader.HISTORICAL_PINS:
            path = nested / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.symlink_to(self.root / name)
        with self.assertRaisesRegex(ValueError, "escapes"):
            portable_reader.verify_v2(nested)


if __name__ == "__main__":
    unittest.main()
