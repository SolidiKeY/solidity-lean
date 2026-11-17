#!/usr/bin/env python3
"""Self-test of scripts/heartbeats/collect.sh: kernel work is counted, repeated
runs agree, and the ratchet fails only on growth beyond its tolerance."""
import json, os, subprocess, tempfile, unittest

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
COLLECT = os.path.join(ROOT, "scripts", "heartbeats", "collect.sh")
RATCHET = os.path.join(ROOT, "scripts", "heartbeats", "collect.d", "ratchet.py")
FIXTURE = "tests/heartbeats/Fixture.lean"


def collect(*args):
    p = subprocess.run(["bash", COLLECT, *args], cwd=ROOT, capture_output=True, text=True)
    return p.returncode, [json.loads(l) for l in p.stdout.splitlines() if l.strip()], p.stderr


def cmds(row):
    return {c["name"] or c["kind"]: c["heartbeats"] for c in row["commands"]}


class Collector(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.runs = [collect(FIXTURE) for _ in range(2)]

    def test_kernel_counted(self):
        rc, rows, err = self.runs[0]
        self.assertEqual(rc, 0, err)
        row, = rows
        c = cmds(row)
        self.assertEqual(list(c), ["sumTo", "heavy", "light", "example"])
        self.assertEqual([x["line"] for x in row["commands"]], [5, 7, 9, 11])
        # `heavy` is mostly kernel work: far above `light`, which has the same shape.
        self.assertGreater(c["heavy"], 5 * c["light"])
        self.assertAlmostEqual(row["heartbeats"], sum(c.values()), places=2)
        # The asynchronous elaborator moves the proof off the counting thread.
        exe = os.path.join(ROOT, ".lake", "build", "bin", "hbcollect")
        env = {k: v for k, v in os.environ.items() if k != "LEAN_NUM_THREADS"}
        p = subprocess.run(["lake", "env", exe, "--async", FIXTURE, "tests.heartbeats.Fixture"],
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
            rc, _, err = collect("--write", base, FIXTURE)
            self.assertEqual(rc, 0, err)
            with open(base) as f:
                modules = json.load(f)["modules"]
            self.assertIn("heavy", modules["tests.heartbeats.Fixture"]["commands"])
            rc, _, err = collect("--check", base, FIXTURE)
            self.assertEqual(rc, 0, err)


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
