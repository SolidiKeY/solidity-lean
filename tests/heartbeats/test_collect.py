#!/usr/bin/env python3
"""Self-test of scripts/heartbeats/collect.sh: kernel work is counted, repeated
runs agree, the ratchet fails only on growth beyond its tolerance, and `--lake`
makes the counted elaboration the module's Lake build."""
import hashlib, json, os, shutil, subprocess, tempfile, unittest

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
COLLECT = os.path.join(ROOT, "scripts", "heartbeats", "collect.sh")
RATCHET = os.path.join(ROOT, "scripts", "heartbeats", "collect.d", "ratchet.py")
# The fixture is written to a temporary directory (tests/ takes no new Lean lines).
# The `decide +kernel` proofs are checked by the kernel alone, so they are counted
# only when elaboration is synchronous (`Elab.async=false`).
FIXTURE_SOURCE = """\
-- heartbeat collector fixture

def sumTo (n : Nat) : Nat := (List.range n).foldl (· + ·) 0

theorem heavy : sumTo 400 = 79800 := by decide +kernel

theorem light : sumTo 4 = 6 := by decide +kernel

example : True := trivial
"""


def collect(*args, script=COLLECT, cwd=ROOT, env=None):
    p = subprocess.run(["bash", script, *args], cwd=cwd, capture_output=True, text=True, env=env)
    return p.returncode, [json.loads(l) for l in p.stdout.splitlines() if l.strip()], p.stderr


def cmds(row):
    return {c["name"] or c["kind"]: c["heartbeats"] for c in row["commands"]}


class Collector(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.fixture = os.path.join(cls.tmp.name, "Fixture.lean")
        with open(cls.fixture, "w") as f:
            f.write(FIXTURE_SOURCE)
        cls.runs = [collect(cls.fixture) for _ in range(2)]

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_kernel_counted(self):
        rc, rows, err = self.runs[0]
        self.assertEqual(rc, 0, err)
        row, = rows
        c = cmds(row)
        self.assertEqual(list(c), ["sumTo", "heavy", "light", "example"])
        self.assertEqual([x["line"] for x in row["commands"]], [3, 5, 7, 9])
        # `heavy` is mostly kernel work: far above `light`, which has the same shape.
        self.assertGreater(c["heavy"], 5 * c["light"])
        self.assertAlmostEqual(row["heartbeats"], sum(c.values()), places=2)
        # The asynchronous elaborator moves the proof off the counting thread.
        exe = os.path.join(ROOT, ".lake", "build", "bin", "hbcollect")
        env = {k: v for k, v in os.environ.items() if k != "LEAN_NUM_THREADS"}
        p = subprocess.run(["lake", "env", exe, "--async", self.fixture, "Fixture"],
                           cwd=ROOT, capture_output=True, text=True, env=env, timeout=300)
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertLess(cmds(json.loads(p.stdout))["heavy"], c["heavy"] / 5)

    def test_deterministic(self):
        (_, a, _), (_, b, _) = self.runs
        self.assertTrue(a)
        self.assertEqual([(r["heartbeats"], r["commands"]) for r in a],
                         [(r["heartbeats"], r["commands"]) for r in b])

    def test_ratchet_roundtrip(self):
        with tempfile.TemporaryDirectory() as d:
            base = os.path.join(d, "base.json")
            rc, _, err = collect("--write", base, self.fixture)
            self.assertEqual(rc, 0, err)
            with open(base) as f:
                modules = json.load(f)["modules"]
            self.assertIn("heavy", modules["Fixture"]["commands"])
            rc, _, err = collect("--check", base, self.fixture)
            self.assertEqual(rc, 0, err)


# A Lake project of its own for `--lake` (written to a temporary directory): the
# checkout's collector and driver by link, a library whose `Fix.B` imports `Fix.A`, and
# the artifact cache switched on as in the checkout's lakefile.
LAKEFILE = """\
name = "fix"
enableArtifactCache = true

[[lean_lib]]
name = "Fix"
weakLeanArgs = ["--tstack=131072"]

[[lean_exe]]
name = "hbcollect"
root = "Tools.Heartbeats.Main"
supportInterpreter = true
"""
DEPENDENT_SOURCE = """\
import Fix.A

theorem uses : sumTo 4 + 0 = 6 := light

def twice (n : Nat) : Nat := 2 * sumTo n
"""
BAD_SOURCE = "theorem bad : 1 = 2 := rfl\n"


def digest(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


class LakeBuild(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.proj = proj = os.path.join(cls.tmp.name, "proj")
        os.makedirs(os.path.join(proj, "Fix"))
        os.makedirs(os.path.join(proj, "Tools", "Heartbeats"))
        os.makedirs(os.path.join(proj, "scripts"))
        os.symlink(os.path.join(ROOT, "scripts", "heartbeats"), os.path.join(proj, "scripts", "heartbeats"))
        os.symlink(os.path.join(ROOT, "Tools", "Heartbeats", "Main.lean"),
                   os.path.join(proj, "Tools", "Heartbeats", "Main.lean"))
        shutil.copy(os.path.join(ROOT, "lean-toolchain"), proj)
        for name, text in [("lakefile.toml", LAKEFILE), ("Fix/A.lean", FIXTURE_SOURCE),
                           ("Fix/B.lean", DEPENDENT_SOURCE), ("Fix/Bad.lean", BAD_SOURCE)]:
            with open(os.path.join(proj, name), "w") as f:
                f.write(text)
        # A cache of its own: the fixture's artifacts stay out of the checkout's Lake cache.
        cls.env = dict(os.environ, LAKE_CACHE_DIR=os.path.join(cls.tmp.name, "cache"))
        cls.script = os.path.join(proj, "scripts", "heartbeats", "collect.sh")

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def collect(self, *args):
        return collect(*args, script=self.script, cwd=self.proj, env=self.env)

    def lake(self, *args):
        return subprocess.run(["lake", *args], cwd=self.proj, capture_output=True, text=True,
                              env=self.env, timeout=600)

    def test_one_elaboration_is_the_lake_build(self):
        lib = os.path.join(self.proj, ".lake", "build", "lib", "lean", "Fix")
        olean = os.path.join(lib, "A.olean")
        rc, plain, err = self.collect("Fix/A.lean")
        self.assertEqual(rc, 0, err)
        self.assertFalse(os.path.exists(olean))  # the plain collector writes no artifact
        self.assertNotEqual(self.lake("build", "--no-build", "Fix.A").returncode, 0)

        # One run: the same counts as the plain collector, and Lake's artifacts.
        rc, rows, err = self.collect("--lake", "Fix.A")
        self.assertEqual(rc, 0, err)
        row, = rows
        self.assertEqual((row["module"], row["file"], row["errors"]), ("Fix.A", "Fix/A.lean", 0))
        self.assertEqual((row["heartbeats"], row["commands"]), (plain[0]["heartbeats"], plain[0]["commands"]))

        # Lake, with the real `lean`, takes the module as current ...
        p = self.lake("build", "--no-build", "Fix.A")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        # ... and the .olean is byte for byte what `lean` writes when it elaborates synchronously.
        ref = os.path.join(self.tmp.name, "ref.olean")
        p = subprocess.run(["lean", "--tstack=131072", "-DElab.async=false", "Fix/A.lean", "-o", ref],
                           cwd=self.proj, capture_output=True, text=True, env=self.env, timeout=300)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        before = (digest(olean), os.stat(olean).st_mtime_ns)
        self.assertEqual(before[0], digest(ref))

        # A dependent module builds against it without elaborating it again.
        p = self.lake("build", "Fix.B")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("Built Fix.B", p.stdout)
        self.assertNotIn("Built Fix.A", p.stdout)
        self.assertEqual((digest(olean), os.stat(olean).st_mtime_ns), before)
        self.assertTrue(os.path.exists(os.path.join(lib, "B.olean")))

        # Up to date: Lake runs nothing, so there is no line, and that is not a failure.
        rc, rows, err = self.collect("--lake", "Fix.A")
        self.assertEqual((rc, rows), (0, []), err)
        self.assertIn("not elaborated", err)

    def test_errors_leave_no_artifact(self):
        rc, rows, err = self.collect("--lake", "Fix.Bad")
        self.assertEqual(rc, 1, err)
        row, = rows
        self.assertGreater(row["errors"], 0)
        self.assertIn("Fix/Bad.lean:1", err)  # Lake prints the driver's messages
        self.assertFalse(os.path.exists(os.path.join(self.proj, ".lake", "build", "lib", "lean", "Fix", "Bad.olean")))
        self.assertNotEqual(self.lake("build", "--no-build", "Fix.Bad").returncode, 0)


def ratchet(mode, base, rows, *extra):
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as f:
        f.write("".join(json.dumps(r) + "\n" for r in rows))
    try:
        return subprocess.run(["python3", RATCHET, mode, base, f.name, *extra], capture_output=True, text=True)
    finally:
        os.unlink(f.name)


def row(total, **decls):
    return {"module": "M", "errors": 0, "heartbeats": total,
            "commands": [{"line": i, "kind": "theorem", "name": n, "heartbeats": h}
                         for i, (n, h) in enumerate(decls.items(), 1)]}


class Ratchet(unittest.TestCase):
    def check(self, base_row, new_row, *extra):
        with tempfile.TemporaryDirectory() as d:
            base = os.path.join(d, "b.json")
            self.assertEqual(ratchet("write", base, [base_row]).returncode, 0)
            return ratchet("check", base, [new_row], *extra)

    def test_within_tolerance(self):
        self.assertEqual(self.check(row(1000, a=500, b=500), row(1005, a=505, b=500)).returncode, 0)

    def test_module_growth_fails(self):
        p = self.check(row(1000, a=500), row(1100, a=500))
        self.assertEqual(p.returncode, 1)
        self.assertIn("FAIL M:", p.stdout)

    def test_declaration_growth_fails(self):
        p = self.check(row(10000, a=500, b=9500), row(10000, a=600, b=9400))
        self.assertEqual(p.returncode, 1)
        self.assertIn("FAIL M a", p.stdout)
        self.assertIn("decrease M b", p.stdout)

    def test_tolerance_flag(self):
        self.assertEqual(self.check(row(1000, a=500), row(1100, a=500), "--tolerance", "20").returncode, 0)

    def test_new_removed_and_decrease_only_print(self):
        p = self.check(row(1000, a=500, b=400), row(900, a=500, c=300))
        self.assertEqual(p.returncode, 0, p.stdout)
        self.assertIn("removed M b", p.stdout)
        self.assertIn("new M c", p.stdout)
        self.assertIn("decrease M:", p.stdout)

    def test_errors_fail(self):
        bad = dict(row(1000, a=500), errors=1)
        self.assertEqual(self.check(row(1000, a=500), bad).returncode, 1)


if __name__ == "__main__":
    unittest.main()
