"""Guard against truncated, tampered or escaping handoff receipts; external tool controls only."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[4] / "scripts/h62/item2/audit-calculus/handoff_index.py"
spec = importlib.util.spec_from_file_location("handoff_index", SCRIPT)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)


class HandoffIndexControls(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        for name in helper.REQUIRED:
            (self.root / name).write_text("synthetic tool-control bytes " + name)
        self.seal()

    def seal(self):
        self.lines = [hashlib.sha256((self.root / n).read_bytes()).hexdigest() + "  " + n
                      for n in sorted(helper.REQUIRED)]
        (self.root / "SHA256SUMS").write_text("\n".join(self.lines) + "\n")

    def test_positive_bounded_summary(self):
        result = helper.build_index(self.root)
        self.assertEqual(result["verified_entries"], 4)
        self.assertEqual(set(result["selected_artifacts"]), helper.REQUIRED)
        self.assertIn("no coordinator retrieval", result["boundary"])

    def test_tamper_rejected(self):
        (self.root / "HANDOFF.md").write_text("changed")
        with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_missing_rejected(self):
        (self.root / "gates.json").unlink()
        with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_duplicate_rejected(self):
        (self.root / "SHA256SUMS").write_text("\n".join(self.lines + self.lines[:1]))
        with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_parent_path_rejected(self):
        (self.root / "SHA256SUMS").write_text("0" * 64 + "  ../escape")
        with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_symlink_rejected(self):
        target = self.root / "HANDOFF.md"
        target.unlink()
        target.symlink_to(self.root / "gates.json")
        with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_omitted_required_rejected(self):
        (self.root / "SHA256SUMS").write_text("\n".join(self.lines[:1]))
        with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_manifest_limit_rejected(self):
        (self.root / "SHA256SUMS").write_text("x" * 32769)
        with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_changed_manifest_rejected(self):
        original = helper.checked_read
        def mutate(path, limit=None):
            result = original(path, limit)
            if path.name == "HANDOFF.md":
                with (self.root / "SHA256SUMS").open("a") as stream:
                    stream.write("changed\n")
            return result
        with patch.object(helper, "checked_read", side_effect=mutate):
            with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_changed_artifact_during_read_rejected(self):
        original = helper.os.fstat
        calls = 0
        def mutate(descriptor):
            nonlocal calls
            calls += 1
            if calls == 2:
                (self.root / "SHA256SUMS").write_text("changed")
            return original(descriptor)
        with patch.object(helper.os, "fstat", side_effect=mutate):
            with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_extra_tampered_artifact_rejected(self):
        p = self.root / "extra.log"
        p.write_text("before")
        with (self.root / "SHA256SUMS").open("a") as stream:
            stream.write(hashlib.sha256(p.read_bytes()).hexdigest() + "  extra.log\n")
        p.write_text("after")
        with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_self_reference_rejected(self):
        with (self.root / "SHA256SUMS").open("a") as stream:
            stream.write("0" * 64 + "  SHA256SUMS\n")
        with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_manifest_symlink_rejected(self):
        p = self.root / "SHA256SUMS"
        p.rename(self.root / "checksums.copy")
        p.symlink_to(self.root / "checksums.copy")
        with self.assertRaises(ValueError): helper.build_index(self.root)

    def test_entry_limit_rejected(self):
        lines = list(self.lines)
        for i in range(61):
            name = "extra" + str(i)
            (self.root / name).write_bytes(b"same")
            lines.append(hashlib.sha256(b"same").hexdigest() + "  " + name)
        (self.root / "SHA256SUMS").write_text("\n".join(lines))
        with self.assertRaises(ValueError): helper.build_index(self.root)


if __name__ == "__main__": unittest.main()
