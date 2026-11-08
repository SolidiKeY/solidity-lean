"""Guard H109 full-tree observations against cache/tool/source substitution.

Small synthetic filesystem fixtures only; no Lean, Docker or measurements.
"""

import os
import hashlib
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


M = runpy.run_path(str(Path(__file__).with_name("input-inventory.py")))


class Inputs(unittest.TestCase):
    def test_symlink_components_before_parent_traversal(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "outside").write_bytes(b"lexical decoy")
            os.symlink(".", root / "sub")
            os.symlink("sub/../outside", root / "escape")
            with self.assertRaisesRegex(ValueError, "Escaping input symlink"):
                M["inventory"](root)
            (root / "escape").unlink()
            (root / "sub").unlink()
            (root / "actual/deep").mkdir(parents=True)
            (root / "actual/sibling").write_bytes(b"actual target")
            os.symlink("actual/deep", root / "sub")
            os.symlink("sub/../sibling", root / "valid")
            observed = M["inventory"](root)
            self.assertTrue(observed["records"])
            # Revisiting one link after '..' is valid, not necessarily a cycle.
            os.symlink("sub/../../sub/../sibling", root / "revisit")
            self.assertTrue(M["inventory"](root)["records"])

    def test_cli_pin_and_output_ownership(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            root = base / "input"
            root.mkdir()
            (root / "file").write_bytes(b"fixture")
            manifest = base / "inventory.json"
            script = str(Path(__file__).with_name("input-inventory.py"))
            def run(*args):
                return subprocess.run([sys.executable, script, str(root), *map(str, args)],
                                      capture_output=True, text=True)
            self.assertEqual(run("--output", manifest).returncode, 0)
            pin = hashlib.sha256(manifest.read_bytes()).hexdigest()
            self.assertEqual(run("--verify", manifest, "--expected-sha256", pin).returncode, 0)
            for args in [("--verify", manifest),
                         ("--verify", manifest, "--expected-sha256", "0" * 64)]:
                failed = run(*args)
                self.assertNotEqual(failed.returncode, 0)
                self.assertIn("Inventory receipt pin mismatch", failed.stderr)
            failed = run("--output", root / "unsafe.json")
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn("outside the input tree", failed.stderr)
            self.assertFalse((root / "unsafe.json").exists())

    def test_complete_tree_and_drift(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "nested").mkdir()
            path = root / "nested/cache.olean"
            path.write_bytes(b"fixture, never loaded")
            os.symlink("nested/cache.olean", root / "internal-link")
            before = M["inventory"](root)
            self.assertEqual(len(before["records"]), 4)
            self.assertEqual(M["verify"](root, before), before)
            stamp = path.stat().st_mtime_ns
            path.write_bytes(b"different fixture")
            os.utime(path, ns=(stamp, stamp))
            with self.assertRaisesRegex(ValueError, "identity drift"):
                M["verify"](root, before)
            path.write_bytes(b"fixture, never loaded")
            before = M["inventory"](root)
            path.chmod(0o755)
            with self.assertRaisesRegex(ValueError, "identity drift"):
                M["verify"](root, before)
            before = M["inventory"](root)
            (root / "extra").write_bytes(b"new input")
            with self.assertRaisesRegex(ValueError, "identity drift"):
                M["verify"](root, before)

    def test_untrusted_entries(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            os.mkfifo(root / "pipe")
            with self.assertRaisesRegex(ValueError, "special input"):
                M["inventory"](root)
            (root / "pipe").unlink()
            os.symlink("/etc/passwd", root / "escape")
            with self.assertRaisesRegex(ValueError, "Escaping input"):
                M["inventory"](root)
            (root / "escape").unlink()
            os.symlink("missing", root / "dangling")
            with self.assertRaisesRegex(ValueError, "Dangling input symlink"):
                M["inventory"](root)
            (root / "dangling").unlink()
            os.symlink("cycle", root / "cycle")
            with self.assertRaisesRegex(ValueError, "Cyclic input symlink"):
                M["inventory"](root)

    def test_streaming_and_external_hardlink_flag(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            root = base / "input"
            root.mkdir()
            source = root / "large"
            with source.open("wb") as stream:
                for _ in range(20):
                    stream.write(b"x" * 262144)
            os.link(source, base / "external-alias")
            counts = []
            original = os.read
            def read(fd, count):
                counts.append(count)
                return original(fd, count)
            with patch("os.read", read):
                observed = M["inventory"](root)
            self.assertGreater(len(counts), 20)
            self.assertLessEqual(max(counts), 262144)
            self.assertEqual(observed["externalHardlinkAliases"], ["large"])

    def test_directory_swap_never_follows_replacement(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            root, foreign = base / "input", base / "foreign"
            root.mkdir()
            foreign.mkdir()
            (foreign / "outside").write_bytes(b"must not traverse")
            inner = root / "inner"
            inner.mkdir()
            (inner / "inside").write_bytes(b"expected")
            inode = inner.stat().st_ino
            original = os.listdir
            swapped = False
            def listdir(fd):
                nonlocal swapped
                if isinstance(fd, int) and os.fstat(fd).st_ino == inode and not swapped:
                    inner.rename(root / "moved")
                    os.symlink(foreign, inner)
                    swapped = True
                return original(fd)
            with patch("os.listdir", listdir), self.assertRaisesRegex(ValueError, "Input changed during observation"):
                M["inventory"](root)
            self.assertTrue(swapped)

    def test_xattrs_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "input"
            path.write_bytes(b"bytes")
            # The runner refuses unsupported attribute inspection. This control
            # deliberately fails if this filesystem cannot preserve the input.
            os.setxattr(path, "user.h109", b"before")
            before = M["inventory"](root)
            os.setxattr(path, "user.h109", b"after")
            with self.assertRaisesRegex(ValueError, "identity drift"):
                M["verify"](root, before)


if __name__ == "__main__":
    unittest.main()
