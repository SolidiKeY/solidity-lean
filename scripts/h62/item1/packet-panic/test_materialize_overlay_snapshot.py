import pathlib
import subprocess
import sys
import tempfile
import unittest

DIRECTORY = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(DIRECTORY))
from materialize_overlay_snapshot import materialize, verify_extracted
from verify_overlay_snapshot import tree_entries

class MaterializeTest(unittest.TestCase):
    def test_unregistered_snapshot_and_preservation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            repo = root / "repo"
            repo.mkdir()
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            (repo / "nested").mkdir()
            (repo / "nested" / "x.lean").write_text("def x := 1\n")
            (repo / "tool.sh").write_text("#!/bin/sh\n")
            (repo / "tool.sh").chmod(0o755)
            subprocess.run(["git", "add", "nested/x.lean", "tool.sh"], cwd=repo, check=True)
            subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "fixture"], cwd=repo, check=True)
            commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
            before = subprocess.check_output(["git", "worktree", "list", "--porcelain"], cwd=repo)
            archive, dest = root / "snapshot.tar", root / "snapshot"
            result = materialize(repo, commit, archive, dest)
            self.assertEqual(result["files"], 2)
            self.assertEqual((dest / "nested" / "x.lean").read_text(), "def x := 1\n")
            self.assertFalse((dest / ".git").exists())
            (dest / "nested" / "x.lean").write_text("tampered")
            with self.assertRaisesRegex(ValueError, "bytes differ"):
                verify_extracted(dest, tree_entries(repo, commit))
            (dest / "nested" / "x.lean").write_text("def x := 1\n")
            verify_extracted(dest, tree_entries(repo, commit))
            dest.chmod(0o755)
            with self.assertRaisesRegex(ValueError, "root is not a private"):
                verify_extracted(dest, tree_entries(repo, commit))
            dest.chmod(0o700)
            executable = dest / "tool.sh"
            executable.chmod(0o644)
            with self.assertRaisesRegex(ValueError, "file mode differs"):
                verify_extracted(dest, tree_entries(repo, commit))
            executable.chmod(0o755)
            directory = dest / "nested"
            directory.chmod(0o755)
            with self.assertRaisesRegex(ValueError, "directory is not private"):
                verify_extracted(dest, tree_entries(repo, commit))
            directory.chmod(0o700)
            file = directory / "x.lean"
            file.chmod(0o666)
            with self.assertRaisesRegex(ValueError, "file mode differs"):
                verify_extracted(dest, tree_entries(repo, commit))
            file.chmod(0o644)
            verify_extracted(dest, tree_entries(repo, commit))
            self.assertEqual(subprocess.check_output(["git", "worktree", "list", "--porcelain"], cwd=repo), before)
            existing = archive.read_bytes()
            with self.assertRaises(FileExistsError): materialize(repo, commit, archive, dest)
            self.assertEqual(archive.read_bytes(), existing)
            missing_target = root / "not-created.tar"
            symlink = root / "broken.tar"
            symlink.symlink_to(missing_target)
            with self.assertRaises(FileExistsError): materialize(repo, commit, symlink, root / "another")
            self.assertFalse(missing_target.exists())
            destination_link = root / "destination-link"
            destination_link.symlink_to(root / "not-created-directory")
            new_archive = root / "not-created-archive.tar"
            with self.assertRaises(FileExistsError): materialize(repo, commit, new_archive, destination_link)
            self.assertFalse(new_archive.exists())

if __name__ == "__main__": unittest.main()
