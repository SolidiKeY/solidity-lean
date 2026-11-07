import hashlib
from pathlib import Path
import tempfile
import unittest
from verify_manifest import verify

class ManifestControls(unittest.TestCase):
    def fixture(self, name="case.lean"):
        return {"schema_version":1,"files":[{"path":name,"sha256":hashlib.sha256(b"original").hexdigest()}]}
    def test_content_change_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/"case.lean").write_bytes(b"original")
            self.assertEqual(verify(root,self.fixture()),1)
            (root/"case.lean").write_bytes(b"changed")
            with self.assertRaises(ValueError): verify(root,self.fixture())
    def test_escaping_and_absolute_paths_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            for name in ("../case.lean","/case.lean"):
                with self.assertRaises(ValueError): verify(Path(tmp),self.fixture(name))
    def test_empty_and_duplicate_manifest_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/"case.lean").write_bytes(b"original")
            with self.assertRaises(ValueError): verify(root,{"schema_version":1,"files":[]})
            m=self.fixture(); m["files"]*=2
            with self.assertRaises(ValueError): verify(root,m)

if __name__ == "__main__": unittest.main()
