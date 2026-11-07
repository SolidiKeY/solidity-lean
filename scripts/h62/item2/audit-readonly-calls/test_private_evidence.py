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
if __name__=='__main__':unittest.main()
