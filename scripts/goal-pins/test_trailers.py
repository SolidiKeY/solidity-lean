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

    def test_original_trailer_spelling_is_exact(self):
        for spelling in ("Goal-Change:H1", "Goal-Change:    H1", "Goal-Change : H1",
                         "goal-change: H1", "Goal-Change: H1\n continued"):
            with self.subTest(spelling=spelling):
                self.setUp()
                self.commit("change\n\n" + spelling)
                with self.assertRaises(TrailerError):
                    pin_changes(self.repo, self.base, "HEAD")

    def test_canonical_body_line_cannot_validate_malformed_trailer(self):
        self.commit("change\n\nGoal-Change: H1\n\ntext\n\nGoal-Change:H1")
        with self.assertRaises(TrailerError):
            pin_changes(self.repo, self.base, "HEAD")

    def test_canonical_body_line_and_real_trailer_are_accepted(self):
        pin = self.commit("change\n\nGoal-Change: H1\n\ntext\n\nGoal-Change: H1")
        self.assertEqual(pin_changes(self.repo, self.base, "HEAD"), [(pin, "H1")])

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

    def test_non_fast_forward_fails_closed(self):
        pin = self.commit("add pin\n\nGoal-Change: H1")
        with self.assertRaises(TrailerError):
            pin_changes(self.repo, pin, self.base)

    def test_missing_base_fails_closed(self):
        with self.assertRaises(TrailerError):
            pin_changes(self.repo, "does-not-exist", "HEAD")


if __name__ == "__main__":
    unittest.main()
