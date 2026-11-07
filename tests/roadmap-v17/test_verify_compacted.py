import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import tarfile
import io
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('verify_compacted', ROOT / 'scripts/roadmap-v17-verify-compacted.py')
V = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(V)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


class Controls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        source = self.root / 'source.json'
        raw = b'{ "commandExit":125, "buildExit":null, "releaseClosed":true, "ordered":[3,1,2] }'
        source.write_bytes(raw)
        self.out = self.root / 'out'
        self.report = V.C.execute(argparse.Namespace(input=str(source), sha256=sha(raw), member=None,
                                                     archive_sha256=None, out=str(self.out)))

    def tearDown(self):
        self.tmp.cleanup()

    def verify(self, report=None, pin=None, **options):
        receipt = self.out / 'receipt.json'
        if report is not None:
            receipt.write_text(json.dumps(report))
        return V.verify(receipt, pin or sha(receipt.read_bytes()), self.out / 'compact.json', self.out / 'syntax.unverified.json', **options)

    def test_actual_failure_payload_never_promotes(self):
        result = self.verify()
        self.assertIs(result['originalInputRechecked'], False)
        for flag in V.FLAGS:
            self.assertIs(result[flag], False)
        self.assertEqual(json.loads((self.out/'compact.json').read_bytes())['commandExit'], 125)

    def test_regular_original_bytes_rechecked_not_execution(self):
        result = self.verify(original_input=self.root/'source.json')
        self.assertIs(result['originalInputRechecked'], True)
        self.assertIs(result['originalInputEvidence']['historicalFileIdentityAuthenticated'], False)
        for flag in V.FLAGS:
            self.assertIs(result[flag], False)

    def archive(self, name='source.json', kind=tarfile.REGTYPE):
        path = self.root/'original.tar.gz'
        raw = (self.root/'source.json').read_bytes()
        with tarfile.open(path, 'w:gz') as archive:
            member = tarfile.TarInfo(name)
            member.type = kind
            member.size = len(raw) if kind == tarfile.REGTYPE else 0
            member.linkname = 'source.json' if kind == tarfile.SYMTYPE else ''
            archive.addfile(member, io.BytesIO(raw) if member.size else None)
        return path, sha(path.read_bytes())

    def test_archive_original_relocation(self):
        path, pin = self.archive()
        result = self.verify(original_input=path, original_member='source.json', original_archive_sha256=pin)
        self.assertIs(result['originalInputRechecked'], True)
        self.assertEqual(result['originalInputEvidence']['archiveSha256'], pin)
        self.assertIs(result['releaseClosed'], False)

    def test_wrong_archive_pin_or_member(self):
        path, pin = self.archive()
        for member, digest in [('source.json', '0'*64), ('missing.json', pin), ('../source.json', pin)]:
            with self.subTest(member=member, digest=digest), self.assertRaises(ValueError):
                self.verify(original_input=path, original_member=member, original_archive_sha256=digest)

    def test_unsafe_archive_source(self):
        for name, kind in [('../source.json', tarfile.REGTYPE), ('source.json', tarfile.SYMTYPE)]:
            path, pin = self.archive(name, kind)
            with self.subTest(name=name, kind=kind), self.assertRaises(ValueError):
                self.verify(original_input=path, original_member='source.json', original_archive_sha256=pin)

    def test_changed_missing_or_symlink_original(self):
        source = self.root/'source.json'
        raw = source.read_bytes()
        source.write_bytes(raw.replace(b'125', b'0'))
        with self.assertRaises(ValueError):
            self.verify(original_input=source)
        source.unlink()
        with self.assertRaises(OSError):
            self.verify(original_input=source)
        target = self.root/'saved.json'
        target.write_bytes(raw)
        source.symlink_to(target)
        with self.assertRaises(OSError):
            self.verify(original_input=source)

    def test_semantically_equal_whitespace_is_not_exact_original(self):
        source = self.root/'source.json'
        source.write_bytes(source.read_bytes()+b' ')
        with self.assertRaisesRegex(ValueError, 'SHA256'):
            self.verify(original_input=source)

    def test_supported_attachment_counts_do_not_replace_original_check(self):
        changed = copy.deepcopy(self.report)
        changed['bytes']['inputBytes'] += 1
        # Old attachment-only mode explicitly leaves this original claim unverified.
        self.assertIs(self.verify(changed)['originalInputRechecked'], False)
        with self.assertRaisesRegex(ValueError, 'disagreement'):
            self.verify(changed, original_input=self.root/'source.json')

    def test_original_locator_options_are_paired(self):
        for options in [dict(original_member='x'), dict(original_archive_sha256='0'*64),
                        dict(original_input=self.root/'source.json', original_member='x'),
                        dict(original_input=self.root/'source.json', original_archive_sha256='0'*64)]:
            with self.subTest(options=options), self.assertRaises(ValueError):
                self.verify(**options)

    def test_receipt_mutations(self):
        cases = [('schema', True), ('schema', 2), ('status', 'pass'), ('accountingOnly', False),
                 ('jsonSyntaxValidated', False)] + [(k, True) for k in V.FLAGS]
        for key, value in cases:
            with self.subTest(key=key):
                changed = copy.deepcopy(self.report)
                changed[key] = value
                with self.assertRaises(ValueError):
                    self.verify(changed)

    def test_missing_fields(self):
        for key in list(V.FLAGS) + ['schema', 'bytes', 'input', 'ceilings', 'observedProcessLimits']:
            with self.subTest(key=key):
                changed = copy.deepcopy(self.report)
                del changed[key]
                with self.assertRaises((ValueError, KeyError)):
                    self.verify(changed)

    def test_wrong_receipt_pin(self):
        with self.assertRaises(ValueError):
            self.verify(pin='0'*64)

    def test_limits_counts_and_original_pin(self):
        mutations = [(['ceilings','cpuSeconds'], 61), (['ceilings','cpuSeconds'], True),
                     (['observedProcessLimits','cpu'], [60,61]), (['observedProcessLimits','cpu'], [True,60]),
                     (['bytes','inputBytes'], 0), (['bytes','compactBytes'], True), (['bytes','syntaxBytes'], -1),
                     (['bytes','inputBytes'], V.C.MAX_INPUT+1), (['input','expectedSha256'], '0'*64)]
        for path, value in mutations:
            changed = copy.deepcopy(self.report)
            changed[path[0]][path[1]] = value
            with self.subTest(path=path, value=value), self.assertRaises(ValueError):
                self.verify(changed)

    def test_missing_and_corrupted_attachments(self):
        for name in ['compact.json', 'syntax.unverified.json']:
            path = self.out/name
            original = path.read_bytes()
            path.write_bytes(original[:-1])
            with self.assertRaises(ValueError):
                self.verify()
            path.unlink()
            with self.assertRaises(OSError):
                self.verify()
            path.write_bytes(original)

    def test_forged_matching_hash_but_different_bytes(self):
        raw = (self.out/'compact.json').read_bytes().replace(b'125', b'126')
        (self.out/'compact.json').write_bytes(raw)
        changed = copy.deepcopy(self.report)
        changed['bytes'].update(compactBytes=len(raw), compactSha256=sha(raw))
        with self.assertRaisesRegex(ValueError, 'disagreement'):
            self.verify(changed)

    def test_invalid_original_tokens_not_repaired(self):
        raw = b'[1 2]'
        compact = b'[12]'
        (self.out/'compact.json').write_bytes(compact)
        (self.out/'syntax.unverified.json').write_bytes(raw)
        changed = copy.deepcopy(self.report)
        changed['bytes'].update(compactBytes=len(compact), compactSha256=sha(compact), syntaxBytes=len(raw), syntaxSha256=sha(raw))
        with self.assertRaises(ValueError):
            self.verify(changed)

    def test_duplicate_receipt_keys(self):
        receipt = self.out/'receipt.json'
        raw = receipt.read_bytes().replace(b'"schema": 1', b'"schema": 1, "schema": 1')
        receipt.write_bytes(raw)
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            self.verify()

    def test_non_utf8_receipts_and_attachments(self):
        for encoding in ['utf-16', 'utf-32']:
            with self.subTest(encoding=encoding):
                receipt = self.out/'receipt.json'
                raw = json.dumps(self.report).encode(encoding)
                receipt.write_bytes(raw)
                with self.assertRaises((UnicodeError, ValueError)):
                    self.verify()
                encoded = '{"x":1}'.encode(encoding)
                (self.out/'compact.json').write_bytes(encoded)
                (self.out/'syntax.unverified.json').write_bytes(encoded)
                changed = copy.deepcopy(self.report)
                changed['bytes'].update(inputBytes=len(encoded), compactBytes=len(encoded), syntaxBytes=len(encoded),
                                        compactSha256=sha(encoded), syntaxSha256=sha(encoded))
                with self.assertRaises((UnicodeError, ValueError)):
                    self.verify(changed)

    def test_pending_or_unlinked_publication(self):
        receipt = self.out/'receipt.json'
        pin = sha(receipt.read_bytes())
        pending = self.out/'receipt.pending.json'
        pending.write_bytes(receipt.read_bytes())
        with self.assertRaisesRegex(ValueError, 'unpublished'):
            V.verify(pending, pin, self.out/'compact.json', self.out/'syntax.unverified.json')
        other = self.root/'compact.json'
        other.write_bytes((self.out/'compact.json').read_bytes())
        with self.assertRaisesRegex(ValueError, 'unlinked'):
            V.verify(receipt, pin, other, self.out/'syntax.unverified.json')

    def test_symlink_attachment(self):
        path = self.out/'compact.json'
        path.rename(self.out/'saved')
        path.symlink_to(self.out/'saved')
        with self.assertRaises(OSError):
            self.verify()


if __name__ == '__main__':
    unittest.main()
