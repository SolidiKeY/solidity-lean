"""Checksum IO equivalence and unsupported-filesystem controls."""
import errno,hashlib,importlib.util,os,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2]
s=importlib.util.spec_from_file_location('resources',ROOT/'scripts/roadmap-v17-resources.py');r=importlib.util.module_from_spec(s);s.loader.exec_module(r)
class HashIoControls(unittest.TestCase):
    def test_sizes_and_unaligned_tail(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'input'
            for size in [0,1,4095,4096,4097,2*1024*1024+17]:
                raw=(bytes(range(256))*((size+255)//256))[:size];p.write_bytes(raw)
                with self.subTest(size=size):self.assertEqual(r.hash_file(p),hashlib.sha256(raw).hexdigest());self.assertEqual(p.read_bytes(),raw)
    def test_unsupported_direct_read_falls_back_without_fabricated_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'input';p.write_bytes(b'published source bytes')
            with patch.object(os,'open',side_effect=OSError(errno.EINVAL,'unsupported direct IO')):
                self.assertEqual(r.hash_file(p),hashlib.sha256(p.read_bytes()).hexdigest())
    def test_input_change_is_not_accepted(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'input';p.write_bytes(b'one');before=p.stat();p.write_bytes(b'two bytes');after=p.stat()
            with patch.object(Path,'stat',side_effect=[before,after]),self.assertRaises(ValueError):r.hash_file(p)
    def test_git_blob_and_sha256_match_actual_bytes_and_fallback(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'input'
            for size in [0,1,4095,4096,4097,1024*1024+17]:
                raw=(bytes(range(256))*((size+255)//256))[:size];p.write_bytes(raw)
                expected={'sha256':hashlib.sha256(raw).hexdigest(),'gitBlob':hashlib.sha1(b'blob '+str(size).encode()+b'\0'+raw).hexdigest()}
                with self.subTest(size=size):
                    self.assertEqual(r.hash_blob(p),expected)
                    with patch.object(os,'open',side_effect=OSError(errno.EINVAL,'unsupported direct IO')):self.assertEqual(r.hash_blob(p),expected)
                    self.assertEqual(p.read_bytes(),raw)
    def test_git_blob_input_change_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'input';p.write_bytes(b'one');before=p.stat();p.write_bytes(b'two bytes');after=p.stat()
            with patch.object(Path,'stat',side_effect=[before,after]),self.assertRaises(ValueError):r.hash_blob(p)
if __name__=='__main__':unittest.main()
