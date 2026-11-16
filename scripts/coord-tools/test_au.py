#!/usr/bin/env python3
"""Unit tests for au.py --diff (stdlib only; builds throwaway git repositories)."""
import io, contextlib, os, subprocess, sys, tempfile, unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import au

PROOF = """theorem {name} (a b c d m : Int) (left : a % m = b % m)
    (right : c % m = d % m) : (a * c) % m = (b * d) % m := by
  rw [Int.mul_emod a c m, Int.mul_emod b d m, left, right]
  simp only [Int.add_comm, Int.mul_comm, Int.emod_emod_of_dvd, left, right]
  exact {name}_helper a b c d m left right
"""

PY = """def denominator(lines, hook):
    total = 0
    for line in lines:
        if hook(line) and not line.strip().startswith("#"):
            total += len(line.split()) + 1
    return total
"""


def sh(cwd, *args):
    subprocess.run(args, cwd=cwd, check=True, capture_output=True)


class DiffMode(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.r = self.tmp.name
        sh(self.r, "git", "init", "-q", "-b", "master")
        sh(self.r, "git", "config", "user.email", "t@t")
        sh(self.r, "git", "config", "user.name", "t")
        self.write("Src/A.lean", PROOF.format(name="mul_congr"))
        self.write("scripts/tool", "#!/usr/bin/env python3\n" + PY)
        self.base = self.commit("base")
        self.cache = os.path.join(self.r, ".git", "au.sqlite")

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        p = os.path.join(self.r, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w") as f:
            f.write(text)

    def commit(self, msg):
        sh(self.r, "git", "add", "-A")
        sh(self.r, "git", "commit", "-q", "-m", msg)
        return subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.r, capture_output=True, text=True).stdout.strip()

    def run_diff(self, head, t=20):
        return au.diff_mode(self.r, self.base, head, min_save=t, cache_path=self.cache)

    def test_renamed_copy_in_other_directory_is_found(self):
        self.write("Other/B.lean", "namespace X\n\n" + PROOF.format(name="mul_congr2"))
        res = self.run_diff(self.commit("copy"))
        self.assertTrue(res)
        c = res[0]
        self.assertEqual(c["added"][0], "Other/B.lean")
        self.assertIn("Src/A.lean", [o[0] for o in c["others"]])
        self.assertEqual(c["holes"], 2)  # name and name_helper, each renamed consistently

    def test_unrelated_addition_is_quiet(self):
        self.write("Other/C.lean", "def f (x : Nat) : Nat :=\n  x + 1\n\ndef g : Nat := 3\n")
        self.assertEqual(self.run_diff(self.commit("new")), [])

    def test_threshold(self):
        self.write("Other/B.lean", PROOF.format(name="mul_congr2"))
        head = self.commit("copy")
        best = self.run_diff(head)[0]["save"]
        self.assertEqual(self.run_diff(head, best + 1), [])

    def test_extensionless_python_script(self):
        self.write("scripts/backtest.py", "import sys\n\n" + PY.replace("total", "acc"))
        res = self.run_diff(self.commit("py copy"))
        self.assertTrue(any(c["added"][0] == "scripts/backtest.py" and
                            any(o[0] == "scripts/tool" for o in c["others"]) for c in res))

    def test_comments_do_not_count(self):
        self.write("Other/D.lean", "/-\n" + PROOF.format(name="mul_congr") + "-/\n")
        self.assertEqual(self.run_diff(self.commit("comment")), [])

    def test_exit_codes(self):
        self.write("Other/B.lean", PROOF.format(name="mul_congr2"))
        head = self.commit("copy")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(au.diff_main([self.base, head, "--repo", self.r, "--cache", self.cache, "--min-save", "20"]), 1)
            self.assertEqual(au.diff_main([self.base, head, "--repo", self.r, "--cache", self.cache, "--min-save", "9999"]), 0)
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(au.diff_main([self.base, "nosuchrev", "--repo", self.r, "--cache", self.cache]), 2)


if __name__ == "__main__":
    unittest.main()
