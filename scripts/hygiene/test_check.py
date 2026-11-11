#!/usr/bin/env python3
"""Regression tests for scripts/hygiene/check.py on temporary Git repositories.

Each test builds real base/head/merge history and runs the checker's command line, asserting
its exit status (0 pass, 1 policy failure, 2 setup error) and the decisive message. All data is
generated in a temporary directory and removed afterwards.
"""
import json, os, subprocess, sys, tempfile, unittest

CHECK = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check.py")
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(CHECK))
import check  # noqa: E402

LIMIT = 200 * 1024
ENV = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid",
       "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid",
       "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}
ENV.pop("HYGIENE_BASE", None)


class Repo:
    def __init__(self, d): self.d = d

    def git(self, *a, inp=None):
        r = subprocess.run(["git", *a], cwd=self.d, env=ENV, input=inp, capture_output=True)
        if r.returncode: raise AssertionError(f"fixture git {a}: {r.stderr.decode()}")
        return r.stdout.decode().strip()

    def write(self, path, data):
        full = os.path.join(self.d, path)
        os.makedirs(os.path.dirname(full) or self.d, exist_ok=True)
        with open(full, "wb") as f: f.write(data if isinstance(data, bytes) else data.encode())

    def rm(self, path): self.git("rm", "-q", "--", path)

    def commit(self, files=None, msg="c"):
        for p, d in (files or {}).items(): self.write(p, d)
        self.git("add", "-A"); self.git("commit", "-q", "--allow-empty", "-m", msg)
        return self.git("rev-parse", "HEAD")

    def master(self, sha): self.git("update-ref", "refs/remotes/origin/master", sha)

    def run(self, *args):
        r = subprocess.run([sys.executable, "-B", CHECK, *args], cwd=self.d, env=ENV, capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr

    def seed(self, rev):
        code, out = self.run("seed", "--rev", rev)
        assert code == 0, out
        return out


def lines(n, tag="x"): return "".join(f"{tag}{i}\n" for i in range(n))


class Base(unittest.TestCase):
    """A base tree with legacy offenders, and a lane commit that introduces their seed."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.r = Repo(self.tmp.name)
        self.r.git("init", "-q", "-b", "main")
        self.base = self.r.commit({
            "README.md": "hello\n",
            "tests/h62/item5/a.txt": "legacy\n",
            "tests/h62/b.txt": "legacy\n",
            "docs/roadmap-g03-ledger.md": "legacy\n",
            "old/big.bin": b"\0" * (LIMIT + 10),
            "keep/ok.txt": lines(10),
        }, "base")
        self.r.master(self.base)
        self.r.write("scripts/hygiene/allow.json", self.r.seed(self.base))
        self.intro = self.r.commit(msg="introduce allow.json")

    def tearDown(self): self.tmp.cleanup()

    def established(self):
        """Make the current head (the introduction, at first) origin/master; later commits compare with it."""
        self.r.master(self.r.git("rev-parse", "HEAD"))

    def allow(self):
        with open(os.path.join(self.r.d, "scripts/hygiene/allow.json")) as f: return json.load(f)

    def set_allow(self, a):
        self.r.write("scripts/hygiene/allow.json", json.dumps(a, indent=1))

    def ok(self):
        code, out = self.r.run()
        self.assertEqual(code, 0, out); self.assertIn("hygiene: PASS", out)
        return out

    def fails(self, *needles, code=1):
        c, out = self.r.run()
        self.assertEqual(c, code, out)
        for n in needles: self.assertIn(n, out)
        return out


class Seed(Base):
    def test_introduction_bound_to_merge_base_passes(self):
        self.ok()
        a = self.allow()
        self.assertEqual(a["seed"], self.base)
        self.assertEqual(a["paths"], ["docs/roadmap-g03-ledger.md", "tests/h62"])
        self.assertEqual(a["bytes"], {"old/big.bin": LIMIT + 10})

    def test_seed_from_candidate_with_new_offender_rejected(self):
        self.r.git("reset", "-q", "--hard", self.base)
        lane = self.r.commit({"tests/h99/new.txt": "x\n"})
        self.r.write("scripts/hygiene/allow.json", self.r.seed(lane))
        self.r.commit()
        self.fails("not an ancestor of")

    def test_introduction_with_extra_entry_rejected(self):
        self.r.git("reset", "-q", "--hard", self.base)
        a = json.loads(self.r.seed(self.base)); a["bytes"]["keep/ok.txt"] = 50
        self.set_allow(a); self.r.commit()
        self.fails("bytes entry 'keep/ok.txt'", "differs from the seed")

    def test_introduction_missing_entry_rejected(self):
        self.r.git("reset", "-q", "--hard", self.base)
        a = json.loads(self.r.seed(self.base)); a["paths"].remove("tests/h62")
        self.set_allow(a); self.r.commit()
        self.fails("differs from the seed", "'tests/h62/b.txt'")

    def test_seed_mode_does_not_write(self):
        before = self.allow()
        self.r.run("seed", "--rev", self.intro); self.r.run()
        self.assertEqual(before, self.allow())
        self.assertEqual(self.r.git("status", "--porcelain"), "")


class Size(Base):
    def test_exactly_at_limit_passes_binary(self):
        self.r.commit({"data/at.bin": b"\xff\0" * (LIMIT // 2)}); self.ok()

    def test_one_byte_over_fails_binary(self):
        self.r.commit({"data/over.bin": b"\xff" * (LIMIT + 1)})
        self.fails("FAIL size 'data/over.bin': 204801 bytes over the 204800-byte (200 KB) limit",
                   "coord-evidence", "committed generator")

    def test_whitespace_path(self):
        self.r.commit({"data/a b\tc.txt": "y" * (LIMIT + 1)})
        self.fails("FAIL size 'data/a b\\tc.txt'")

    def test_lean_excluded(self):
        self.r.commit({"Solidity/Big.lean": "-- x\n" * 60000}); self.ok()

    def test_legacy_may_shrink_not_grow(self):
        self.established()
        self.r.commit({"old/big.bin": b"\0" * (LIMIT + 5)}); self.ok()
        self.r.commit({"old/big.bin": b"\0" * (LIMIT + 11)})
        self.fails("its legacy exception stops at 204810 bytes")

    def test_renamed_legacy_blob_fails(self):
        self.established()
        self.r.git("mv", "old/big.bin", "old/big2.bin"); self.r.commit()
        self.fails("FAIL size 'old/big2.bin'")


class Lines(Base):
    def setUp(self):
        super().setUp(); self.established()

    def test_exactly_at_limit_passes(self):
        self.r.commit({"gen/a.txt": lines(20000)}); self.ok()

    def test_one_over_fails(self):
        self.r.commit({"gen/a.txt": lines(20001)})
        self.fails("non-.lean paths add 20001 lines over 1 file(s)", "+20001 gen/")

    def test_split_over_files_and_dirs_fails(self):
        self.r.commit({f"gen{i}/part{j}.csv": lines(2001, f"{i}{j}") for i in range(2) for j in range(5)})
        self.fails("add 20010 lines over 10 file(s)", "+10005 gen0/", "+10005 gen1/")

    def test_split_over_commits_fails(self):
        self.r.commit({"gen/a.txt": lines(15000)}); self.r.commit({"gen/b.txt": lines(5001)})
        self.fails("add 20001 lines")

    def test_deletions_do_not_cancel(self):
        self.r.commit({"keep/old.txt": lines(30000)}); self.established()
        self.r.rm("keep/old.txt"); self.r.commit({"gen/a.txt": lines(20001, "y")})
        self.fails("add 20001 lines")

    def test_rewrite_counts_added_lines(self):
        self.r.commit({"keep/old.txt": lines(20000)}); self.established()
        self.r.commit({"keep/old.txt": lines(20001, "y")})
        self.fails("add 20001 lines")

    def test_binary_newlines_count(self):
        self.r.commit({"gen/a.bin": b"\0\n" * 20001}); self.fails("add 20001 lines")

    def test_lean_excluded(self):
        self.r.commit({"Solidity/Gen.lean": lines(30000)}); self.ok()

    def test_exact_binary_rename_adds_nothing(self):
        self.r.commit({"keep/old.bin": b"\0\n" * 20001}); self.established()
        self.r.git("mv", "keep/old.bin", "keep/moved.bin"); self.r.commit()
        self.ok()

    def test_exact_rename_adds_nothing(self):
        self.r.commit({"keep/old.txt": lines(15000)}); self.established()
        self.r.git("mv", "keep/old.txt", "keep/moved.txt"); self.r.commit({"gen/a.txt": lines(10000)})
        self.ok()


class Paths(unittest.TestCase):
    BAD = {
        "tests/h62/a.txt": "h62", "H7/x.md": "H7", "docs/h62-handoff.md": "h62-handoff.md",
        "a/g18_notes/x": "g18_notes", "Solidity/G16/X.lean": "G16", "x/v13-serial.toml": "v13-serial.toml",
        "docs/notes.v2.md": "notes.v2.md", "a/item5": "item5", "tests/ITEM12/x": "ITEM12",
        "docs/roadmap-g00-scope.md": "roadmap-g00-scope.md", "Roadmap_x/y": "Roadmap_x",
        "tests/directruntime-20261104/x": "directruntime-20261104",
        "a/run-20261105T1200Z/x": "run-20261105T1200Z", "a/x~h3/y": "x~h3",
    }
    GOOD = ["h2o.txt", "a/ipv6/x", "items5/x", "vector/x", "Solidity/FrozenV1.lean", "roadmaps-x/y",
            "docs/roadmap.md", "a/x-202611040/y", "notes-20261104.md", "a/x-2025110/y", "sha256.txt",
            "a/G18Graph.lean", "a/node~h3x/y", "item/x", "h/x", "a/hv2/x", "a/v/x", "x-2026110/y"]

    def test_families(self):
        for p, seg in self.BAD.items():
            self.assertEqual(check.offending_segment(p)[1], seg, p)

    def test_controls(self):
        for p in self.GOOD:
            self.assertIsNone(check.offending_segment(p), p)

    def test_prefix_stops_at_first_offending_segment(self):
        self.assertEqual(check.offending_segment("tests/h62/item5/a.txt")[0], "tests/h62")


class PathRatchet(Base):
    def test_new_offender_fails(self):
        self.r.commit({"tests/h99/x.txt": "x\n"})
        self.fails("FAIL path 'tests/h99/x.txt': segment 'h99' names a process or batch ID and is not a legacy",
                   "allow.json (it only shrinks)")

    def test_ordinary_names_pass(self):
        self.r.commit({p: "x\n" for p in Paths.GOOD}); self.ok()

    def test_new_descendant_of_legacy_dir_fails(self):
        self.established()
        self.r.commit({"tests/h62/new.txt": "x\n"})
        self.fails("'tests/h62/new.txt'", "new path under legacy prefix 'tests/h62'")

    def test_legacy_file_may_change(self):
        self.established()
        self.r.commit({"tests/h62/b.txt": "edited\n"}); self.ok()

    def test_rename_onto_offending_name_fails(self):
        self.established()
        self.r.git("mv", "keep/ok.txt", "keep/v3.txt"); self.r.commit()
        self.fails("'keep/v3.txt': segment 'v3.txt'")

    def test_rename_of_legacy_file_fails(self):
        self.established()
        self.r.git("mv", "docs/roadmap-g03-ledger.md", "docs/roadmap-g03-ledger2.md"); self.r.commit()
        self.fails("'docs/roadmap-g03-ledger2.md'")

    def test_rename_out_of_offending_name_passes(self):
        self.established()
        self.r.git("mv", "docs/roadmap-g03-ledger.md", "docs/ledger.md"); self.r.commit(); self.ok()


class AllowRatchet(Base):
    def setUp(self):
        super().setUp(); self.established()

    def test_removal_allowed(self):
        self.r.rm("docs/roadmap-g03-ledger.md"); self.r.rm("old/big.bin")
        a = self.allow(); a["paths"].remove("docs/roadmap-g03-ledger.md"); a["bytes"] = {}
        self.set_allow(a); self.r.commit(); self.ok()

    def test_fabricated_entry_rejected(self):
        self.r.commit({"tests/h99/x.txt": "x\n"})
        a = self.allow(); a["paths"] = sorted(a["paths"] + ["tests/h99"]); self.set_allow(a); self.r.commit()
        self.fails("not an offending prefix of seed", "adds path exception 'tests/h99'")

    def test_broadening_bytes_rejected(self):
        a = self.allow(); a["bytes"]["old/big.bin"] += 1000; self.set_allow(a); self.r.commit()
        self.fails("rewrites bytes exception 'old/big.bin'")

    def test_broadening_prefix_rejected(self):
        a = self.allow(); a["paths"] = sorted(a["paths"] + ["tests"]); self.set_allow(a); self.r.commit()
        self.fails("adds path exception 'tests'")

    def test_reintroduction_after_removal_rejected(self):
        a = self.allow(); a["paths"].remove("tests/h62"); self.set_allow(a)
        self.r.rm("tests/h62/b.txt"); self.r.rm("tests/h62/item5/a.txt")
        self.r.master(self.r.commit(msg="master drops h62"))
        self.r.commit({"tests/h62/b.txt": "back\n"})
        a["paths"] = sorted(a["paths"] + ["tests/h62"]); self.set_allow(a); self.r.commit()
        self.fails("adds path exception 'tests/h62'")

    def test_new_seed_identifier_rejected(self):
        lane = self.r.commit({"tests/h99/x.txt": "x\n"})
        self.r.write("scripts/hygiene/allow.json", self.r.seed(lane)); self.r.commit()
        self.fails("changes the seed")

    def test_deleting_allowlist_rejected(self):
        self.r.rm("scripts/hygiene/allow.json"); self.r.commit()
        self.fails("allow.json is missing", code=2)

    def test_delete_then_reintroduce_rejected(self):
        self.r.rm("scripts/hygiene/allow.json"); self.r.commit()
        self.r.write("scripts/hygiene/allow.json", self.r.seed(self.intro)); self.r.commit()
        self.fails("deletes scripts/hygiene/allow.json", "reintroduces scripts/hygiene/allow.json")

    def test_merge_parent_bypass_rejected(self):
        # A side branch broadens the allowlist and is merged; the merge keeps its version.
        side = self.r.git("rev-parse", "HEAD")
        self.r.commit({"tests/h99/x.txt": "x\n"})
        a = self.allow(); a["paths"] = sorted(a["paths"] + ["tests/h99"]); self.set_allow(a)
        broad = self.r.commit(msg="side broadens")
        self.r.git("checkout", "-q", "-b", "lane", side); self.r.commit({"README.md": "lane\n"})
        self.r.git("merge", "-q", "--no-edit", broad)
        self.fails("adds path exception 'tests/h99'")

    def test_merge_of_unrelated_introduction_rejected(self):
        # A history without allow.json introduces its own seed (of a tree with a new offender),
        # then is merged into a lane; the merge takes that allowlist.
        self.r.git("checkout", "-q", "-b", "other", self.base)
        other = self.r.commit({"tests/h99/x.txt": "x\n"})
        self.r.write("scripts/hygiene/allow.json", self.r.seed(other)); self.r.commit(msg="other intro")
        self.r.git("checkout", "-q", "-b", "lane", self.intro)
        self.r.git("merge", "-q", "--no-edit", "-X", "theirs", "other")
        self.fails("changes the seed")

    def test_merge_of_branch_older_than_allowlist_passes(self):
        self.r.git("checkout", "-q", "-b", "old", self.base); self.r.commit({"old.txt": "x\n"})
        self.r.git("checkout", "-q", "main"); self.r.git("merge", "-q", "--no-edit", "old")
        self.ok()

    def test_new_gitlink_offender_fails(self):
        self.r.git("update-index", "--add", "--cacheinfo", f"160000,{self.base},tests/h99")
        self.r.git("commit", "-q", "-m", "gitlink")
        self.fails("'tests/h99'")

    def test_merge_of_master_into_lane_passes(self):
        self.r.git("checkout", "-q", "-b", "lane"); self.r.commit({"lane.txt": "x\n"})
        self.r.git("checkout", "-q", "main"); self.r.rm("tests/h62/b.txt")
        self.r.master(self.r.commit(msg="master moves"))
        self.r.git("checkout", "-q", "lane"); self.r.git("merge", "-q", "--no-edit", "main")
        self.ok()

    def test_on_master_uses_first_parent(self):
        self.r.commit({"tests/h99/x.txt": "x\n"})
        self.r.master(self.r.git("rev-parse", "HEAD"))
        self.fails("base " + self.intro[:12], "'tests/h99/x.txt'")


class Setup(Base):
    def test_unknown_base_is_actionable(self):
        c, out = self.r.run("--base", "deadbeef")
        self.assertEqual(c, 2, out); self.assertIn("fetch full history", out)

    def test_no_origin_master_is_actionable(self):
        self.r.git("update-ref", "-d", "refs/remotes/origin/master")
        c, out = self.r.run(); self.assertEqual(c, 2, out); self.assertIn("git fetch origin master", out)

    def test_malformed_allowlist_is_actionable(self):
        self.r.commit({"scripts/hygiene/allow.json": "{not json"})
        self.fails("is not JSON", code=2)

    def test_wrong_shape_is_actionable(self):
        self.set_allow({"seed": self.base, "paths": "tests/h62", "bytes": {}}); self.r.commit()
        self.fails("is malformed", code=2)

    def test_missing_seed_commit_is_actionable(self):
        a = self.allow(); a["seed"] = "1" * 40; self.set_allow(a); self.r.commit()
        self.fails("is not in this clone", code=2)

    def test_shallow_clone_is_actionable(self):
        with tempfile.TemporaryDirectory() as d:
            subprocess.run(["git", "clone", "-q", "--depth", "1", "file://" + self.r.d, d], env=ENV, check=True)
            c = subprocess.run([sys.executable, "-B", CHECK], cwd=d, env=ENV, capture_output=True, text=True)
            self.assertEqual(c.returncode, 2); self.assertIn("shallow clone", c.stderr)


if __name__ == "__main__":
    unittest.main()
