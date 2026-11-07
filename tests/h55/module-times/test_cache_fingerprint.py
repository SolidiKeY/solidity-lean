import importlib.util
import os
import pathlib
import tempfile
import unittest
from unittest.mock import patch

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/cache_fingerprint.py"
spec = importlib.util.spec_from_file_location("cache_fingerprint", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class CacheFingerprint(unittest.TestCase):
    def test_reproducible_and_content_complete(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            (root / "b").mkdir()
            (root / "b" / "x.olean").write_bytes(b"abc")
            (root / "a.trace").write_bytes(b"z")
            before = module.fingerprint(root)
            self.assertEqual(["a.trace", "b/x.olean"], [x["path"] for x in before["files"]])
            self.assertEqual(before, module.fingerprint(root))
            (root / "b" / "x.olean").write_bytes(b"abd")
            self.assertNotEqual(before["manifest_sha256"], module.fingerprint(root)["manifest_sha256"])
            prior = module.fingerprint(root)
            (root / "empty-directory").mkdir()
            self.assertNotEqual(prior["manifest_sha256"], module.fingerprint(root)["manifest_sha256"])
            (root / "new.ilean").write_bytes(b"")
            self.assertNotEqual(2, len(module.fingerprint(root)["files"]))

    def test_mutation_during_read_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            target = root / "cache.olean"
            target.write_bytes(b"original bytes")
            original_read = module.os.read
            changed = False
            def mutate(fd, size):
                nonlocal changed
                result = original_read(fd, size)
                if result and not changed:
                    changed = True
                    target.write_bytes(b"replacement bytes")
                return result
            with patch.object(module.os, "read", side_effect=mutate), self.assertRaises(ValueError):
                module.fingerprint(root)

    def test_symlink_nonregular_and_relative_roots_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            (root / "link").symlink_to("missing")
            with self.assertRaises(ValueError):
                module.fingerprint(root)
            (root / "link").unlink()
            os.mkfifo(root / "pipe")
            with self.assertRaises(ValueError):
                module.fingerprint(root)
            with self.assertRaises(ValueError):
                module.fingerprint(pathlib.Path("relative"))


if __name__ == "__main__":
    unittest.main()
