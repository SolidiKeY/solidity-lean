#!/usr/bin/env python3
"""Guard H127 raw source copies against filtered, dirty or externally linked input."""
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("snapshot", Path(__file__).with_name("source-snapshot.py"))
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)


class SnapshotTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.repo = self.root / "source"; self.repo.mkdir()
        m.command(self.repo, "init", "--quiet")
        m.command(self.repo, "config", "user.name", "Snapshot controls")
        m.command(self.repo, "config", "user.email", "snapshot@example.invalid")
        (self.repo / "binary").write_bytes(b"\x00\xff\n")
        (self.repo / "ignored").write_text("must remain\n")
        (self.repo / "script").write_text("#!/bin/false\n"); (self.repo / "script").chmod(0o755)
        (self.repo / ".gitattributes").write_text("ignored export-ignore\nsubst export-subst\n")
        (self.repo / "subst").write_text("$Format:%H$\n")
        self.commit()
        (self.repo / "parent").write_text("second commit\n"); self.commit()
        self.head = m.output(self.repo, "rev-parse", "HEAD").strip().decode()
        self.dest = self.root / "snapshot"

    def commit(self):
        m.command(self.repo, "add", "--all")
        m.command(self.repo, "commit", "--quiet", "-m", "fixture")

    def prepare(self):
        return m.materialize(self.repo, self.head, self.dest)

    def test_raw_blobs_private_shallow_git_and_source_unchanged(self):
        (self.repo / "binary").write_bytes(b"dirty")
        (self.repo / "untracked").write_text("absent")
        before = m.output(self.repo, "status", "--porcelain=v1")
        result = self.prepare(); work = self.dest / "repo"
        self.assertEqual((work / "binary").read_bytes(), b"\x00\xff\n")
        self.assertTrue((work / "ignored").exists())
        self.assertEqual((work / "subst").read_text(), "$Format:%H$\n")
        self.assertFalse((work / "untracked").exists())
        self.assertEqual((work / "script").stat().st_mode & 0o777, 0o755)
        self.assertFalse((work / ".git/objects/info/alternates").exists())
        self.assertEqual((work / ".git/shallow").read_text(), self.head + "\n")
        self.assertEqual(m.output(work, "rev-parse", "HEAD").strip().decode(), self.head)
        self.assertEqual(before, m.output(self.repo, "status", "--porcelain=v1"))
        self.assertFalse(result["immutableMountAuthenticated"])
        self.assertEqual(m.verify(self.dest, result["manifestSha256"]), result)

    def test_existing_destination_refused(self):
        self.dest.mkdir()
        with self.assertRaises(FileExistsError): self.prepare()

    def test_symlink_input_refused_before_output(self):
        (self.repo / "link").symlink_to("binary"); self.commit()
        self.head = m.output(self.repo, "rev-parse", "HEAD").strip().decode()
        with self.assertRaisesRegex(ValueError, "nonregular"): self.prepare()
        self.assertFalse(self.dest.exists())

    def test_nonexact_commit_and_unsafe_paths(self):
        with self.assertRaisesRegex(ValueError, "exact SHA1"): m.entries(self.repo, "HEAD")
        for name in ("/absolute", "../escape", "x/../escape", "x/.GiT/config", "control\n", "x//y"):
            with self.assertRaises(ValueError): m.safe_path(name)

    def test_manifest_pin_and_file_mutations(self):
        result = self.prepare(); digest = result["manifestSha256"]
        with self.assertRaisesRegex(ValueError, "manifest hash"): m.verify(self.dest, "0" * 64)
        (self.dest / "repo/binary").write_bytes(b"bad")
        with self.assertRaisesRegex(ValueError, "inventory mismatch"): m.verify(self.dest, digest)

    def test_extra_symlink_and_hardlink_refused(self):
        result = self.prepare(); work = self.dest / "repo"
        (work / "extra").symlink_to("/etc/passwd")
        with self.assertRaisesRegex(ValueError, "unsafe snapshot"): m.verify(self.dest, result["manifestSha256"])
        (work / "extra").unlink(); os.link(work / "binary", work / "extra")
        with self.assertRaisesRegex(ValueError, "unsafe snapshot"): m.verify(self.dest, result["manifestSha256"])

    def test_root_and_manifest_substitution_refused(self):
        result = self.prepare()
        external = self.root / "external"
        (self.dest / "repo").rename(external)
        (self.dest / "repo").symlink_to(external, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "real directory"):
            m.verify(self.dest, result["manifestSha256"])
        (self.dest / "repo").unlink(); external.rename(self.dest / "repo")
        manifest = self.dest / "manifest.json"
        manifest.rename(self.root / "external.json")
        manifest.symlink_to(self.root / "external.json")
        with self.assertRaisesRegex(ValueError, "unsafe snapshot manifest"):
            m.verify(self.dest, result["manifestSha256"])

    def test_git_pin_and_empty_directory_mutations(self):
        result = self.prepare()
        with patch.object(m, "GIT", "/bin/false"):
            with self.assertRaisesRegex(ValueError, "Git executable hash"):
                m.verify(self.dest, result["manifestSha256"])
        (self.dest / "repo/empty-extra").mkdir()
        with self.assertRaisesRegex(ValueError, "directory inventory mismatch"):
            m.verify(self.dest, result["manifestSha256"])

    def test_capacity_failure_does_not_create_output(self):
        with patch.object(m, "RESERVE", 10**30):
            with self.assertRaisesRegex(ValueError, "disk reserve"): self.prepare()
        self.assertFalse(self.dest.exists())


if __name__ == "__main__": unittest.main()
