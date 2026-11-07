import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/h55/vectors-tables"))
import validate_frozen as runner


class FrozenRunnerIsolationTests(unittest.TestCase):
    def test_tooling_root_and_parent_symlinks_refused_before_git(self):
        for relative in ("scripts", "scripts/h55", "scripts/h55/vectors-tables"):
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as name:
                base = Path(name)
                root = base / "root"
                root.mkdir()
                target = base / "outside"
                target.mkdir()
                link = root / relative
                link.parent.mkdir(parents=True, exist_ok=True)
                link.symlink_to(target, target_is_directory=True)
                with patch.object(runner, "ROOT", root), patch.object(
                        runner, "git", side_effect=AssertionError("Git must not run")):
                    with self.assertRaisesRegex(ValueError, "symlinked tooling directory"):
                        runner.run()

    def test_descendant_symlink_refused_before_git(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            for area in runner.AREAS:
                (root / area).mkdir(parents=True)
            outside = root / "outside"
            outside.write_text("not tooling")
            (root / runner.AREAS[0] / "linked.py").symlink_to(outside)
            with patch.object(runner, "ROOT", root), patch.object(
                    runner, "git", side_effect=AssertionError("Git must not run")):
                with self.assertRaisesRegex(ValueError, "symlinked tooling input"):
                    runner.run()


if __name__ == "__main__":
    unittest.main()
