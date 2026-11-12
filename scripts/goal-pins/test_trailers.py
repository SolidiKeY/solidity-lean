"""Exercise the trailer inspection against actual Git commits and merges."""
import subprocess
import tempfile
import unittest
from pathlib import Path

from trailers import TrailerError, pin_changes


class TrailerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.invalid")
        (self.repo / "readme").write_text("initial\n")
        self.git("add", ".")
        self.git("commit", "-qm", "initial")
        self.base = self.git("rev-parse", "HEAD")
        self.path = self.repo / "Solidity/Goals/Pins.lean"
        self.path.parent.mkdir(parents=True)

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.repo), *args]).decode().strip()

    def commit(self, message, value="pin\n"):
        self.path.write_text(value)
        self.git("add", ".")
        self.git("commit", "-qm", message)
        return self.git("rev-parse", "HEAD")

    def test_valid_and_unchanged_commits(self):
        pin = self.commit("add pin\n\nGoal-Change: H42")
        (self.repo / "readme").write_text("changed\n")
        self.git("add", ".")
        self.git("commit", "-qm", "unrelated")
        self.assertEqual(pin_changes(self.repo, self.base, "HEAD"), [(pin, "H42")])

    def test_missing_or_non_trailer_is_rejected(self):
        self.commit("change\n\nGoal-Change: H42\n\nmore prose")
        with self.assertRaises(TrailerError):
            pin_changes(self.repo, self.base, "HEAD")

    def test_malformed_or_duplicate_is_rejected(self):
        for value in ("H01", "H-1", "H1 extra", "h1", "H1\nGoal-Change: H2"):
            with self.subTest(value=value):
                self.setUp()
                self.commit("change\n\nGoal-Change: " + value)
                with self.assertRaises(TrailerError):
                    pin_changes(self.repo, self.base, "HEAD")

    def test_intermediate_change_cannot_be_hidden_by_revert(self):
        self.commit("add pin", "pin\n")
        self.git("rm", "-q", "Solidity/Goals/Pins.lean")
        self.git("commit", "-qm", "revert\n\nGoal-Change: H4")
        with self.assertRaises(TrailerError):
            pin_changes(self.repo, self.base, "HEAD")

    def test_merge_is_compared_to_each_parent(self):
        branch = self.git("branch", "--show-current")
        self.git("checkout", "-qb", "side")
        self.commit("add pin\n\nGoal-Change: H1")
        self.git("checkout", "-q", branch)
        (self.repo / "readme").write_text("other\n")
        self.git("add", ".")
        self.git("commit", "-qm", "other")
        self.git("merge", "-q", "--no-ff", "side", "-m", "merge")
        with self.assertRaises(TrailerError):
            pin_changes(self.repo, self.base, "HEAD")

    def test_missing_base_fails_closed(self):
        with self.assertRaises(TrailerError):
            pin_changes(self.repo, "does-not-exist", "HEAD")


if __name__ == "__main__":
    unittest.main()
