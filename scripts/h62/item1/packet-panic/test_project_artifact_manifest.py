import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('project_artifact_manifest', Path(__file__).with_name('project_artifact_manifest.py'))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class ManifestTests(unittest.TestCase):
    def test_sorted_and_sensitive_to_contents(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / '.cache').mkdir()
            (root / 'z').write_bytes(b'z')
            (root / '.cache' / 'a').write_bytes(b'a')
            first = module.inventory(root)
            self.assertEqual([f['path'] for f in first['files']], ['.cache/a', 'z'])
            self.assertEqual(first, module.inventory(root))
            (root / 'z').write_bytes(b'x')
            self.assertNotEqual(first, module.inventory(root))

    def test_rejects_dangling_and_directory_symlinks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'link').symlink_to(root / 'missing')
            with self.assertRaises(ValueError):
                module.inventory(root)
            (root / 'link').unlink()
            (root / 'link').symlink_to(root, target_is_directory=True)
            with self.assertRaises(ValueError):
                module.inventory(root)


if __name__ == '__main__':
    unittest.main()
