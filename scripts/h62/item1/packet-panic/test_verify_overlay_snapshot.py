import hashlib
import importlib.util
import io
import pathlib
import subprocess
import tarfile
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("verify_overlay_snapshot", pathlib.Path(__file__).with_name("verify_overlay_snapshot.py"))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class SnapshotTest(unittest.TestCase):
    def test_git_archive_and_negative_controls(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            repo = root / "repo"
            repo.mkdir()
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            (repo / "a.lean").write_text("def a := 1\n")
            (repo / "nested").mkdir()
            (repo / "nested" / "b.lean").write_text("def b := 2\n")
            (repo / "tool.sh").write_text("#!/bin/sh\n")
            (repo / "tool.sh").chmod(0o755)
            subprocess.run(["git", "add", "a.lean", "tool.sh", "nested/b.lean"], cwd=repo, check=True)
            subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "fixture"], cwd=repo, check=True)
            commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
            archive = root / "fixture.tar"
            subprocess.run(["git", "-c", "tar.umask=0022", "archive", "--format=tar", "--output", str(archive), commit], cwd=repo, check=True)
            tree = module.tree_entries(repo, commit)
            self.assertEqual(module.verify_archive(archive, tree), 3)
            with self.assertRaisesRegex(ValueError, "omits"):
                module.verify_archive(archive, {**tree, "missing": ("100644", "0" * 40)})
            with self.assertRaisesRegex(ValueError, "content differs"):
                module.verify_archive(archive, {**tree, "a.lean": ("100644", "0" * 40)})
            with self.assertRaisesRegex(ValueError, "file mode"):
                module.verify_archive(archive, {**tree, "tool.sh": ("100644", tree["tool.sh"][1])})
            for name, link in (("../escape", False), ("a.lean", True)):
                bad = root / ("escape.tar" if not link else "link.tar")
                with tarfile.open(bad, "w") as t:
                    info = tarfile.TarInfo(name)
                    if link:
                        info.type = tarfile.SYMTYPE
                        info.linkname = "outside"
                        t.addfile(info)
                    else:
                        info.size = 1
                        t.addfile(info, io.BytesIO(b"x"))
                with self.assertRaises(ValueError): module.verify_archive(bad, tree)
            bad_mode = root / "bad-dir-mode.tar"
            with tarfile.open(bad_mode, "w") as t:
                info = tarfile.TarInfo("nested")
                info.type = tarfile.DIRTYPE
                info.mode = 0o777
                t.addfile(info)
            with self.assertRaisesRegex(ValueError, "directory mode"):
                module.verify_archive(bad_mode, tree)
            for label, entries in (
                ("extra-dir", [("extra", True), ("a.lean", False)]),
                ("duplicate-dir", [("nested", True), ("nested", True)]),
                ("file-as-dir", [("a.lean", True)]),
                ("duplicate-file", [("a.lean", False), ("a.lean", False)]),
            ):
                bad = root / (label + ".tar")
                with tarfile.open(bad, "w") as t:
                    for name, is_dir in entries:
                        info = tarfile.TarInfo(name)
                        if is_dir:
                            info.type = tarfile.DIRTYPE
                            info.mode = 0o755
                            t.addfile(info)
                        else:
                            data = (repo / name).read_bytes()
                            info.mode = 0o644
                            info.size = len(data)
                            t.addfile(info, io.BytesIO(data))
                with self.assertRaises(ValueError): module.verify_archive(bad, tree)

if __name__ == "__main__": unittest.main()
