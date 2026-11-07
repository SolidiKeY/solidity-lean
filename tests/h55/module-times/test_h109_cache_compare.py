"""Guard regression: changed cache content or metadata is treated as equal."""
import importlib.util
import os
import pathlib
import shutil
import tempfile
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/h109_cache_compare.py"
spec = importlib.util.spec_from_file_location("h109_cache_compare", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class CacheComparison(unittest.TestCase):
    def test_equal_then_content_metadata_and_symlink_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            a, b = root / "a", root / "b"
            a.mkdir()
            (a / "item").write_text("one")
            shutil.copytree(a, b, copy_function=shutil.copy2)
            noop = lambda: None
            self.assertEqual("equal-observation", module.compare(a, b, noop)["status"])
            with self.assertRaisesRegex(ValueError, "distinct"):
                module.compare(a, a, noop)
            with self.assertRaisesRegex(ValueError, "resource stop"):
                module.compare(a, b, lambda: (_ for _ in ()).throw(ValueError("resource stop")))
            (b / "item").unlink()
            os.link(a / "item", b / "item")
            with self.assertRaisesRegex(ValueError, "share filesystem inodes"):
                module.compare(a, b, noop)
            (b / "item").unlink()
            shutil.copy2(a / "item", b / "item")
            (b / "item").write_text("two")
            self.assertEqual("different-observation", module.compare(a, b, noop)["status"])
            shutil.copy2(a / "item", b / "item")
            timestamp = (b / "item").stat().st_mtime_ns
            os.utime(b / "item", ns=(timestamp + 1_000_000_000, timestamp + 1_000_000_000))
            self.assertEqual("different-observation", module.compare(a, b, noop)["status"])
            (b / "link").symlink_to("item")
            with self.assertRaises(ValueError):
                module.compare(a, b, noop)


if __name__ == "__main__":
    unittest.main()
