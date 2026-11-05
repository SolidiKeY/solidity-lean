import argparse
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('compact_json', ROOT / 'scripts/roadmap-v17-compact-json.py')
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


class Controls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.source = self.root / 'input.json'
        self.out = self.root / 'out'

    def tearDown(self):
        self.temp.cleanup()

    def run_record(self, raw, **overrides):
        self.source.write_bytes(raw)
        args = dict(input=str(self.source), sha256=sha(raw), out=str(self.out), member=None, archive_sha256=None)
        args.update(overrides)
        return MOD.execute(argparse.Namespace(**args))

    def assert_nonpromotion(self, report):
        for key in MOD.FLAGS:
            self.assertIs(report[key], False)

    def assert_rejected(self, raw, **overrides):
        with self.assertRaises((ValueError, OSError, UnicodeError)):
            self.run_record(raw, **overrides)
        self.assertFalse((self.out / 'compact.json').exists())
        if (self.out / 'receipt.json').exists():
            report = json.loads((self.out / 'receipt.json').read_text())
            self.assertEqual(report['status'], 'error')
            self.assert_nonpromotion(report)

    def test_values_escapes_and_order_preserved(self):
        # Build valid escaped content independently with the standard serializer.
        obj = {'ordered': [3, 1, 2], 's': 'space \t and " q', 'u': 'α', 'n': 120.0}
        raw = json.dumps(obj, ensure_ascii=True, indent=4).encode()
        report = self.run_record(raw)
        compact = (self.out / 'compact.json').read_bytes()
        self.assertEqual(json.loads(compact), obj)
        self.assertIn(b'\\u03b1', compact)
        self.assertEqual(report['bytes']['inputSha256'], sha(raw))
        self.assertEqual(report['bytes']['compactSha256'], sha(compact))
        self.assert_nonpromotion(report)

    def test_every_chunk_boundary(self):
        obj = {'text': '\\" \n α \\\\', 'rows': [False, None, 12, -3.5]}
        raw = json.dumps(obj, indent=2, ensure_ascii=False).encode()
        for size in range(1, len(raw) + 1):
            with self.subTest(size=size), mock.patch.object(MOD, 'CHUNK', size):
                output = io.BytesIO()
                MOD.compact(io.BytesIO(raw), output, sha(raw))
                self.assertEqual(json.loads(output.getvalue()), obj)

    def test_number_lexemes_preserved(self):
        self.run_record(b'[ 1.2300e+04 , -0 , 5E-2 ]')
        self.assertEqual((self.out / 'compact.json').read_bytes(), b'[1.2300e+04,-0,5E-2]')

    def test_utf16_and_utf32_rejected(self):
        for encoding in ['utf-16', 'utf-32']:
            # Different output directories retain each failure independently.
            self.out = self.root / encoding
            self.assert_rejected('{}' .encode(encoding))

    def test_wrong_pin(self):
        self.assert_rejected(b'{"revision":"old"}', sha256='0' * 64)

    def test_invalid_pin(self):
        self.assert_rejected(b'{}', sha256=True)

    def test_changed_revision_bytes(self):
        self.assert_rejected(b'{"revision":"changed"}', sha256=sha(b'{"revision":"original"}'))

    def test_failed_native_gate_stays_failed_data(self):
        obj = {'commandExit': 125, 'buildExit': None, 'metadata': None, 'revision': 'old'}
        report = self.run_record(json.dumps(obj, indent=3).encode())
        self.assertEqual(json.loads((self.out / 'compact.json').read_text()), obj)
        self.assert_nonpromotion(report)
        self.assertEqual(report['status'], 'data-only')

    def test_forged_proof_flags_not_adopted(self):
        report = self.run_record(b'{"kernelValidated":true,"releaseClosed":true}')
        self.assert_nonpromotion(report)
        self.assertTrue(json.loads((self.out / 'compact.json').read_text())['releaseClosed'])

    def test_truncated(self):
        self.assert_rejected(b'{"x": [1,2]')

    def test_truncated_string(self):
        self.assert_rejected(b'{"x":"unfinished')

    def test_duplicate_key(self):
        self.assert_rejected(b'{"x":1,"x":2}')

    def test_escaped_duplicate_key(self):
        self.assert_rejected(b'{"x":1,"\\u0078":2}')

    def test_nested_duplicate(self):
        self.assert_rejected(b'{"a":[{"x":1,"x":2}]}')

    def test_non_json_constant(self):
        self.assert_rejected(b'{"x":NaN}')

    def test_invalid_utf8(self):
        self.assert_rejected(b'{"x":"\xff"}')

    def test_extra_document(self):
        self.assert_rejected(b'{}{}')

    def test_non_json_whitespace(self):
        self.assert_rejected(b'{\x0b"x":1}')

    def test_input_limit(self):
        with mock.patch.object(MOD, 'MAX_INPUT', 1):
            self.assert_rejected(b'{}')

    def test_compact_limit(self):
        with mock.patch.object(MOD, 'MAX_COMPACT', 1):
            self.assert_rejected(b'{}')

    def test_missing_input(self):
        with self.assertRaises(FileNotFoundError):
            MOD.execute(argparse.Namespace(input=str(self.source), sha256='0'*64, out=str(self.out), member=None, archive_sha256=None))
        self.assertFalse((self.out / 'compact.json').exists())

    def test_symlink_input(self):
        self.source.symlink_to(self.root / 'missing')
        with self.assertRaises(OSError):
            MOD.execute(argparse.Namespace(input=str(self.source), sha256='0'*64, out=str(self.out), member=None, archive_sha256=None))

    def test_existing_output_untouched(self):
        self.out.mkdir()
        (self.out / 'keep').write_bytes(b'kept')
        with self.assertRaises(FileExistsError):
            self.run_record(b'{}')
        self.assertEqual((self.out / 'keep').read_bytes(), b'kept')

    def archive(self, entries):
        path = self.root / 'input.tar.gz'
        with tarfile.open(path, 'w:gz') as archive:
            for name, raw, kind in entries:
                member = tarfile.TarInfo(name)
                member.type = kind
                member.size = len(raw) if kind == tarfile.REGTYPE else 0
                archive.addfile(member, io.BytesIO(raw) if kind == tarfile.REGTYPE else None)
        return path

    def run_archive(self, entries, **overrides):
        path = self.archive(entries)
        args = dict(input=str(path), sha256=sha(b'{ "x" : 1 }'), out=str(self.out), member='record.json', archive_sha256=sha(path.read_bytes()))
        args.update(overrides)
        return MOD.execute(argparse.Namespace(**args))

    def test_pinned_archive(self):
        report = self.run_archive([('record.json', b'{ "x" : 1 }', tarfile.REGTYPE)])
        self.assertEqual((self.out / 'compact.json').read_bytes(), b'{"x":1}')
        self.assertEqual(report['archiveMembers'], 1)
        self.assert_nonpromotion(report)

    def test_bad_archive_pin(self):
        with self.assertRaises(ValueError):
            self.run_archive([('record.json', b'{ "x" : 1 }', tarfile.REGTYPE)], archive_sha256='0'*64)

    def test_bad_member_pin(self):
        with self.assertRaises(ValueError):
            self.run_archive([('record.json', b'{ "x" : 1 }', tarfile.REGTYPE)], sha256='0'*64)

    def test_missing_member(self):
        with self.assertRaises(ValueError):
            self.run_archive([('other.json', b'{}', tarfile.REGTYPE)])

    def test_duplicate_member(self):
        with self.assertRaises(ValueError):
            self.run_archive([('record.json', b'{ "x" : 1 }', tarfile.REGTYPE)]*2)

    def test_unsafe_or_link_member(self):
        for name, kind in [('../x', tarfile.REGTYPE), ('/x', tarfile.REGTYPE), ('x', tarfile.SYMTYPE), ('x', tarfile.LNKTYPE), ('x', tarfile.CHRTYPE)]:
            with self.subTest(name=name, kind=kind), tempfile.TemporaryDirectory() as dest:
                with self.assertRaises(ValueError):
                    self.run_archive([(name, b'{}', kind)], out=str(Path(dest)/'out'))

    def test_member_limit(self):
        with mock.patch.object(MOD, 'MAX_MEMBERS', 0), self.assertRaises(ValueError):
            self.run_archive([('record.json', b'{ "x" : 1 }', tarfile.REGTYPE)])

    def test_changed_input_detected(self):
        original = MOD.compact
        def change(stream, target, expected, validation=None):
            result = original(stream, target, expected, validation)
            self.source.write_bytes(b'{"changed":true}')
            return result
        with mock.patch.object(MOD, 'compact', change):
            self.assert_rejected(b'{}')

    def test_fifo_input(self):
        import os
        os.mkfifo(self.source)
        with self.assertRaises(ValueError):
            MOD.execute(argparse.Namespace(input=str(self.source), sha256='0'*64, out=str(self.out), member=None, archive_sha256=None))

    def test_tool_source_change(self):
        original = Path.read_bytes
        calls = 0
        def changed(path):
            nonlocal calls
            if path == Path(MOD.__file__):
                calls += 1
                return b'original' if calls == 1 else b'changed'
            return original(path)
        with mock.patch.object(Path, 'read_bytes', changed):
            self.assert_rejected(b'{}')

    def test_receipt_commit_failure(self):
        original = Path.rename
        def fail(path, target):
            if path.name == 'receipt.pending.json':
                raise OSError('injected receipt commit failure')
            return original(path, target)
        with mock.patch.object(Path, 'rename', fail):
            self.assert_rejected(b'{}')
        self.assertTrue((self.out / 'compact.unverified.json').exists())

    def test_observed_limits_and_reported_tool_only(self):
        import resource
        report = self.run_record(b'{}')
        self.assertEqual(report['observedProcessLimits']['addressSpace'], list(resource.getrlimit(resource.RLIMIT_AS)))
        self.assertEqual(report['observedProcessLimits']['cpu'], list(resource.getrlimit(resource.RLIMIT_CPU)))
        self.assertFalse(report['toolExecutionAuthenticated'])
        self.assertEqual(report['reportedToolSourceSha256'], sha(Path(MOD.__file__).read_bytes()))

    def test_split_tokens_never_repaired(self):
        for raw in [b'[1 2]', b't rue', b'1 e2', b'- 1', b'[1. 2]', b'{"x":tr ue}']:
            for size in [1, 2, 3, 65536]:
                with self.subTest(raw=raw, size=size), tempfile.TemporaryDirectory() as dest, mock.patch.object(MOD, 'CHUNK', size):
                    self.assert_rejected(raw, out=str(Path(dest)/'out'))

    def test_corrupt_partial_output(self):
        original = Path.read_bytes
        def corrupt(path):
            if path.name == 'compact.unverified.json':
                return b'{"forged":true}'
            return original(path)
        with mock.patch.object(Path, 'read_bytes', corrupt):
            self.assert_rejected(b'{}')

    def test_corrupt_syntax_copy(self):
        original = Path.read_bytes
        def corrupt(path):
            if path.name == 'syntax.unverified.json':
                return b'{"forged":true}'
            return original(path)
        with mock.patch.object(Path, 'read_bytes', corrupt):
            self.assert_rejected(b'{}')

    def test_original_syntax_equivalence_all_boundaries(self):
        obj = {'text': 'literal \t spaces \\" α', 'n': [-10, 1.2e3, None, True]}
        raw = json.dumps(obj, ensure_ascii=False, indent=4).encode()
        for size in range(1, len(raw)+1):
            with self.subTest(size=size), mock.patch.object(MOD, 'CHUNK', size):
                output, syntax = io.BytesIO(), io.BytesIO()
                counts = MOD.compact(io.BytesIO(raw), output, sha(raw), syntax)
                self.assertEqual(json.loads(syntax.getvalue()), obj)
                self.assertEqual(json.loads(output.getvalue()), obj)
                self.assertLessEqual(counts['syntaxBytes'], 2*counts['compactBytes']+1)


if __name__ == '__main__':
    unittest.main()
