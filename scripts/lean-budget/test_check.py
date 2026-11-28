#!/usr/bin/env python3
"""Self-test of check.py on throwaway fixture repositories (run: python3 -B scripts/lean-budget/test_check.py)."""
import importlib.util, json, os, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("lb_check", os.path.join(HERE, "check.py"))
check = importlib.util.module_from_spec(spec); spec.loader.exec_module(check)
CFG = check.load_allow(os.path.join(HERE, "allow.json"))
CFG = dict(CFG, cap=50)  # small cap so the fixtures stay small

REGISTER = 'ROOTS=[\n    ("Solidity.lean",".","Solidity",[],[]),\n]\n'


def g(*a, cwd):
    return subprocess.run(["git", *a], cwd=cwd, check=True, capture_output=True, text=True,
                          env=dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t",
                                   GIT_COMMITTER_EMAIL="t@t")).stdout.strip()


class Fixture(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.d = self.tmp.name
        g("init", "-q", "-b", "master", cwd=self.d)
        self.write("scripts/coord-tools/register.sh", REGISTER)
        self.write("Solidity/Backend/Old.lean", 100)
        self.write("Solidity/Lowering/L.lean", 40)
        self.write("Solidity/Core.lean", 10)
        self.base = self.commit("base")
        self.old = os.getcwd(); os.chdir(self.d)

    def tearDown(self): os.chdir(self.old); self.tmp.cleanup()

    def write(self, path, n):
        p = os.path.join(self.d, path); os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w") as f: f.write(n if isinstance(n, str) else "".join(f"-- {i}\n" for i in range(n)))

    def mv(self, a, b):
        os.makedirs(os.path.dirname(os.path.join(self.d, b)), exist_ok=True); g("mv", a, b, cwd=self.d)

    def commit(self, msg):
        g("add", "-A", cwd=self.d); g("commit", "-q", "--allow-empty", "-m", msg, cwd=self.d)
        return g("rev-parse", "HEAD", cwd=self.d)

    def run_check(self):
        ok, rep = check.evaluate(self.base, "HEAD", CFG)
        return ok, "\n".join(rep)

    def test_frozen_growth_fails(self):
        self.write("Solidity/Backend/Old.lean", 110); self.commit("grow")
        ok, rep = self.run_check()
        self.assertFalse(ok); self.assertIn("frozen area Backend", rep); self.assertIn("grew by 10", rep)
        self.assertIn("Lean-Budget: <step-id>", rep)

    def test_trailer_passes(self):
        self.write("Solidity/Backend/Passes/P.lean", 30); self.write("Solidity/Backend/Passes/XControls.lean", 30)
        self.commit("grow passes\n\nLean-Budget: b1-backend-endpoint")
        self.commit("later")
        ok, rep = self.run_check(); self.assertTrue(ok, rep)

    def test_trailer_only_exempts_its_globs(self):
        self.write("Solidity/Lowering/L.lean", 41); self.commit("x\n\nLean-Budget: b1-backend-endpoint")
        ok, rep = self.run_check(); self.assertFalse(ok); self.assertIn("frozen area Lowering", rep)

    def test_trailer_on_merge_commit_counts(self):
        g("checkout", "-q", "-b", "lane", cwd=self.d)
        self.write("Solidity/Semantics/S.lean", 80); self.commit("lane work")
        g("checkout", "-q", "master", cwd=self.d)
        g("merge", "-q", "--no-ff", "lane", "-m", "Merge lane\n\nLean-Budget: w3-panic-codes", cwd=self.d)
        ok, rep = self.run_check(); self.assertTrue(ok, rep)

    def test_unknown_step_fails(self):
        self.commit("x\n\nLean-Budget: no-such-step")
        ok, rep = self.run_check(); self.assertFalse(ok); self.assertIn("unknown Lean-Budget", rep)

    def test_cap_enforced(self):
        self.write("Solidity/Theory/T.lean", 51); self.commit("big")
        ok, rep = self.run_check(); self.assertFalse(ok); self.assertIn("exceed the per-merge cap 50 by 1", rep)

    def test_cap_at_limit_passes(self):
        self.write("Solidity/Theory/T.lean", 50); self.commit("ok")
        ok, rep = self.run_check(); self.assertTrue(ok, rep)

    def test_shrink_passes(self):
        self.write("Solidity/Backend/Old.lean", 20); self.write("Solidity/Theory/T.lean", 80); self.commit("shrink")
        ok, rep = self.run_check(); self.assertTrue(ok, rep)  # net -80 + 80 = 0

    def test_rename_into_frozen_grows_it(self):
        self.mv("Solidity/Core.lean", "Solidity/Lowering/Core.lean"); self.commit("mv in")
        ok, rep = self.run_check(); self.assertFalse(ok); self.assertIn("Lowering", rep)

    def test_move_out_of_frozen_passes(self):
        self.mv("Solidity/Lowering/L.lean", "Solidity/Shared/L.lean"); self.commit("mv out")
        ok, rep = self.run_check(); self.assertTrue(ok, rep)

    def test_generated_root_not_counted(self):
        self.write("Solidity.lean", 500); self.commit("root")
        ok, rep = self.run_check(); self.assertTrue(ok, rep)

    def test_controls_frozen_anywhere(self):
        self.write("Solidity/Theory/FooControls.lean", 5); self.commit("c")
        ok, rep = self.run_check(); self.assertFalse(ok); self.assertIn("Controls", rep)

    def test_cli_exit_codes(self):
        self.write("Solidity/Lowering/L.lean", 45); self.commit("grow")
        allow = os.path.join(self.d, "allow.json")
        with open(allow, "w") as f: json.dump(CFG, f)
        r = subprocess.run([sys.executable, "-B", os.path.join(HERE, "check.py"), "--base", self.base, "--allow", allow],
                           capture_output=True, text=True, cwd=self.d)
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr); self.assertIn("lean-budget: FAIL", r.stdout)


    def test_per_merge_not_aggregated(self):
        allow = os.path.join(self.d, "allow.json")
        with open(allow, "w") as f: json.dump(CFG, f)
        for i, n in ((1, 30), (2, 30)):  # two merges of +30 each: each under cap 50, sum 60 over it
            g("checkout", "-q", "-b", f"l{i}", cwd=self.d); self.write(f"Solidity/T{i}.lean", n); self.commit(f"l{i}")
            g("checkout", "-q", "master", cwd=self.d); g("merge", "-q", "--no-ff", f"l{i}", "-m", f"m{i}", cwd=self.d)
        run = lambda *x: subprocess.run([sys.executable, "-B", os.path.join(HERE, "check.py"), "--base", self.base,
                                         "--allow", allow, *x], capture_output=True, text=True, cwd=self.d)
        self.assertEqual(run("--per-merge").returncode, 0)
        self.assertEqual(run().returncode, 1)
        # an oversized merge is not hidden by a later shrink in the same push
        g("checkout", "-q", "-b", "l3", cwd=self.d); self.write("Solidity/Big.lean", 80); self.commit("l3")
        g("checkout", "-q", "master", cwd=self.d); g("merge", "-q", "--no-ff", "l3", "-m", "m3", cwd=self.d)
        g("rm", "-q", "Solidity/Big.lean", "Solidity/T1.lean", "Solidity/T2.lean", cwd=self.d); self.commit("shrink")
        self.assertEqual(run().returncode, 0); self.assertEqual(run("--per-merge").returncode, 1)

    def test_strict_aggregate_boundaries(self):
        path = "Solidity/Backend/CompilerOptimizerDomain/Controls.lean"
        for n, expected in ((50, True), (51, False)):
            self.write(path, n); self.commit("O1\n\nLean-Budget: o1-optimizer-domain")
            ok, rep = self.run_check(); self.assertEqual(ok, expected, rep)
            self.assertIn(f"strict aggregate non-generated Lean lines +{n}", rep)

    def test_strict_mixed_paths(self):
        self.write("Solidity/Backend/CompilerOptimizerDomain/P.lean", 30)
        self.write("Solidity/Theory/T.lean", 21)
        self.commit("O1\n\nLean-Budget: o1-optimizer-domain")
        ok, rep = self.run_check(); self.assertFalse(ok, rep)
        self.assertIn("FAIL strict aggregate non-generated Lean lines +51", rep)

    def test_strict_generated_growth(self):
        self.write("Solidity/Backend/CompilerOptimizerDomain/P.lean", 50)
        self.write("Solidity.lean", 1)
        self.commit("O1\n\nLean-Budget: o1-optimizer-domain")
        ok, rep = self.run_check(); self.assertFalse(ok, rep)
        self.assertIn("FAIL strict aggregate including generated Lean lines +51", rep)

    def test_strict_generated_shrink_cannot_offset(self):
        self.write("Solidity.lean", 1); self.base = self.commit("root baseline")
        self.write("Solidity.lean", 0)
        self.write("Solidity/Backend/CompilerOptimizerDomain/P.lean", 51)
        self.commit("O1\n\nLean-Budget: o1-optimizer-domain")
        ok, rep = self.run_check(); self.assertFalse(ok, rep)
        self.assertIn("FAIL strict aggregate non-generated Lean lines +51", rep)
        self.assertIn("ok strict aggregate including generated Lean lines +50", rep)

    def test_strict_keeps_other_frozen_areas(self):
        self.write("Solidity/Lowering/L.lean", 41)
        self.commit("O1\n\nLean-Budget: o1-optimizer-domain")
        ok, rep = self.run_check(); self.assertFalse(ok, rep)
        self.assertIn("FAIL frozen area Lowering", rep)

    def test_strict_opt_in_absent_retains_legacy(self):
        self.write("Solidity/Backend/CompilerOptimizerDomain/P.lean", 51)
        self.commit("O1\n\nLean-Budget: o1-optimizer-domain")
        cfg = dict(CFG); del cfg["strict_aggregate_steps"]
        ok, rep = check.evaluate(self.base, "HEAD", cfg); self.assertTrue(ok, rep)

    def test_strict_merge_and_per_merge(self):
        path = "Solidity/Backend/CompilerOptimizerDomain/P.lean"
        g("checkout", "-q", "-b", "lane", cwd=self.d)
        self.write(path, 51); self.commit("work")
        g("checkout", "-q", "master", cwd=self.d)
        g("merge", "-q", "--no-ff", "lane", "-m",
          "Merge O1\n\nLean-Budget: o1-optimizer-domain", cwd=self.d)
        ok, rep = self.run_check(); self.assertFalse(ok, rep)
        self.assertIn("FAIL strict aggregate", rep)
        self.write(path, 0); self.commit("shrink")
        ok, rep = self.run_check(); self.assertTrue(ok, rep)
        allow = os.path.join(self.d, "allow.json")
        with open(allow, "w") as f: json.dump(CFG, f)
        r = subprocess.run([sys.executable, "-B", os.path.join(HERE, "check.py"),
                            "--base", self.base, "--allow", allow, "--per-merge"],
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("FAIL strict aggregate", r.stdout)

    def test_invalid_strict_selector(self):
        allow = os.path.join(self.d, "allow.json")
        for selector in ("o1-optimizer-domain", [42], ["unknown"], None):
            with self.subTest(selector=selector):
                with open(allow, "w") as f:
                    json.dump(dict(CFG, strict_aggregate_steps=selector), f)
                with self.assertRaisesRegex(ValueError, "strict_aggregate_steps"):
                    check.load_allow(allow)


    def test_yul_stateful_exact_registration_and_cap(self):
        self.write("Solidity/Yul/StatefulRun.lean", 25)
        self.write("Solidity/Yul/StatefulImport.lean", 25)
        self.commit("H2237\n\nLean-Budget: yul-stateful-run")
        ok, rep = self.run_check(); self.assertTrue(ok, rep)
        self.write("Solidity/Yul/StatefulImport.lean", 26)
        self.commit("one line over cap")
        ok, rep = self.run_check(); self.assertFalse(ok, rep)
        self.assertIn("FAIL strict aggregate non-generated Lean lines +51", rep)

    def test_yul_stateful_keeps_other_yul_frozen(self):
        self.write("Solidity/Yul/Unrelated.lean", 1)
        self.commit("H2237\n\nLean-Budget: yul-stateful-run")
        ok, rep = self.run_check(); self.assertFalse(ok, rep)
        self.assertIn("FAIL frozen area Yul", rep)


class Globs(unittest.TestCase):
    def test_globs(self):
        m = check.matches
        self.assertTrue(m("Solidity/Backend/A/B.lean", ["Solidity/Backend/**"]))
        self.assertTrue(m("Solidity/Backend/CompilerTotal.lean", ["Solidity/Backend/Compiler*.lean"]))
        self.assertFalse(m("Solidity/Backend/X/Compiler.lean", ["Solidity/Backend/Compiler*.lean"]))
        self.assertTrue(m("AControls.lean", ["**/*Controls*.lean"]))
        self.assertFalse(m("Solidity/Yulx/A.lean", ["Solidity/Yul/**"]))

    def test_allow_json_steps(self):
        self.assertEqual(set(CFG["steps"]), {"b1-backend-endpoint", "e1-loops", "va2-honest-theorems", "w3-panic-codes",
                                             "e4-hash-bridge", "t0-endpoint-total", "e2a-lower-total",
                                             "e2b-loops-producer", "yv1-yul-layout-view",
                                             "finish-intrinsic-session", "finish-lowering-sim", "finish-panic",
                                             "finish-line", "finish-yul-layout", "calls-program-bridge",
                                             "o1-optimizer-domain", "yul-stateful-run"})
        self.assertEqual(CFG["steps"]["yv1-yul-layout-view"], ["Solidity/Yul/Layout/**"])
        self.assertEqual(CFG["steps"]["finish-intrinsic-session"], ["Solidity/Correctness/IntrinsicSession/**", "Solidity/Semantics/IntrinsicSession/**"])
        self.assertEqual(CFG["steps"]["finish-lowering-sim"], ["Solidity/Correctness/Lowering/Sim/**"])
        self.assertEqual(CFG["steps"]["finish-panic"], ["Solidity/Correctness/Panic/**"])
        self.assertEqual(CFG["steps"]["finish-line"], ["Solidity/Finish/**"])
        self.assertEqual(CFG["steps"]["finish-yul-layout"], ["Solidity/Yul/Layout/**"])
        self.assertEqual(CFG["steps"]["calls-program-bridge"], ["Solidity/Backend/InternalFlow/CallsProgramBridge*.lean"])
        self.assertEqual(CFG["strict_aggregate_steps"], ["o1-optimizer-domain", "yul-stateful-run"])
        self.assertEqual(CFG["steps"]["yul-stateful-run"], ["Solidity/Yul/StatefulRun.lean", "Solidity/Yul/StatefulImport.lean"])
        self.assertEqual(CFG["steps"]["o1-optimizer-domain"], ["Solidity/Backend/CompilerOptimizerDomain.lean", "Solidity/Backend/CompilerOptimizerDomain/**"])



if __name__ == "__main__":
    unittest.main()
