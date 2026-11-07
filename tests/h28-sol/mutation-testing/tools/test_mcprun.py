"""Self-tests of the MCP runner's decisions: no false kill, no false pass.

Synthetic diagnostics here test the classifiers only; they are never
semantic evidence.  Every real outcome comes from a Lean check.
"""
import unittest

import mcprun

ORACLE = """import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound
namespace H28.T
theorem source_link : True := trivial
theorem checked_kill : True := trivial
#print axioms source_link
#print axioms checked_kill
end H28.T
"""
REG = {"target": [3, 100], "oracle": [101, 110]}


def item(line, message, severity="error"):
    return {"line": line, "message": message, "severity": severity}


def axioms(*deps, kill_sig="¬Solidity.Premise.Sound Solidity.Modality.box H28.T.s H28.T.p H28.T.σ"):
    out = [item(107, "H28.T.checked_kill : " + kill_sig, "info")]
    for n in ("source_link", "checked_kill"):
        msg = f"'H28.T.{n}' depends on axioms: [{', '.join(deps)}]" if deps else f"'H28.T.{n}' does not depend on any axioms"
        out.append(item(105, msg, "info"))
    return out


class Assemble(unittest.TestCase):
    def test_regions_disjoint(self):
        for target in ("import A\nX\nY\n", "import A\nX\nY"):
            text, regions = mcprun.assemble("Solidity/Calculus/Rules.lean", target, ORACLE)
            self.assertEqual(regions["target"][1] + 1, regions["oracle"][0])
            self.assertEqual(text.splitlines()[regions["target"][1] - 1], "Y")

    def test_target_inlined_and_import_dropped(self):
        text, regions = mcprun.assemble("Solidity/Calculus/Rules.lean",
                                        "import A\nimport B\nX\nY\n", ORACLE)
        self.assertNotIn("import Solidity.Calculus.Rules", text)
        self.assertEqual(regions["imports"], ["A", "B", "Solidity.Calculus.PremiseSound"])
        lines = text.splitlines()
        self.assertEqual(lines[regions["target"][0] - 1], "X")
        self.assertEqual(lines[regions["oracle"][0] - 1], "namespace H28.T")

    def test_mutation_unique(self):
        with self.assertRaises(ValueError):
            mcprun.mutate("a a", "a", "b")
        with self.assertRaises(ValueError):
            mcprun.mutate("a", "a", "a")
        self.assertEqual(mcprun.mutate("abc", "b", "x"), "axc")


class Proof(unittest.TestCase):
    taclet = "theorem Taclet.ifElseSplit.toStep : x := by\n  simp\n\n#replay_toStep Taclet\n"

    def classify(self, items, affected=("Taclet.requireSimple",)):
        return mcprun.proof_classify(items, REG, list(affected), self.taclet, "rules")["outcome"]

    def test_clean_is_equivalence_not_kill(self):
        self.assertEqual(self.classify([]), "equivalent-certified")

    def test_sorry_never_passes(self):
        self.assertEqual(self.classify([item(105, "declaration uses 'sorry' sorryAx", "warning")]), "error")

    def test_target_error_is_invalid(self):
        self.assertEqual(self.classify([item(50, "unexpected token")]), "invalid-compilation")

    def test_attributed_row_detects(self):
        self.assertEqual(self.classify([
            item(104, "Solidity.Taclet.requireSimple: Tactic `rfl` failed"),
            item(104, "no proof that `Solidity.Taclet.requireSimple` is `Stmt.step`'s rule"),
            item(108, "Unknown constant `Solidity.Taclet.assertSimple.toStep`"),
            item(107, "fail to show termination for\n  Solidity.Taclet.toStep\nwith errors")]), "detected")

    def test_other_constructor_is_not_a_kill(self):
        self.assertEqual(self.classify([
            item(104, "no proof that `Solidity.Taclet.revertBox` is `Stmt.step`'s rule")]), "error")

    def test_cascade_alone_is_not_a_kill(self):
        self.assertEqual(self.classify([item(108, "Unknown constant `Solidity.Taclet.x.toStep`")]), "error")

    def test_unrelated_error_blocks_kill(self):
        self.assertEqual(self.classify([
            item(104, "no proof that `Solidity.Taclet.requireSimple` is `Stmt.step`'s rule"),
            item(109, "out of memory")]), "error")

    def test_hand_theorem_attribution(self):
        self.assertEqual(self.classify([item(102, "unsolved goals")], ["Taclet.ifElseSplit"]), "detected")
        self.assertEqual(self.classify([item(102, "unsolved goals")]), "error")

    def test_runtime_limit_is_not_a_kill(self):
        self.assertEqual(self.classify([
            item(104, "Solidity.Taclet.requireSimple: (deterministic) timeout at `whnf`, maximum number of heartbeats")]),
            "error")

    def test_trust_guard_is_not_a_kill(self):
        self.assertEqual(self.classify([item(104, "H28 TRUST: Solidity.Taclet.requireSimple.toStep depends on sorryAx")]),
                         "error")

    def test_trust_cascade_only_after_attributed_failure(self):
        hand_err = item(102, "unsolved goals")
        trust = item(104, "H28 TRUST: Solidity.Taclet.ifElseSplit.h28link depends on sorryAx")
        self.assertEqual(self.classify([hand_err, trust], ["Taclet.ifElseSplit"]), "detected")
        self.assertEqual(self.classify([trust], ["Taclet.ifElseSplit"]), "error")

    def test_link_command_attribution(self):
        body = "theorem Taclet.x.toStep : True := trivial\nend Solidity\n#h28_toStep_link LeanTaclet ifElseJoin\n"
        reg = {"target": [3, 100], "oracle": [101, 110]}
        r = mcprun.proof_classify([item(103, "Tactic `assumption` failed")], reg, ["LeanTaclet.ifElseJoin"], body, "rules")
        self.assertEqual(r["outcome"], "detected")
        r = mcprun.proof_classify([item(103, "Tactic `assumption` failed")], reg, ["LeanTaclet.other"], body, "rules")
        self.assertEqual(r["outcome"], "error")

    def test_helper_wildcard(self):
        self.assertEqual(self.classify([
            item(104, "no proof that `Solidity.Taclet.localOpAssign` is `Stmt.step`'s rule")], ["*"]), "detected")


class Semantic(unittest.TestCase):
    def test_success_requires_axiom_exports(self):
        self.assertTrue(mcprun.semantic_success(axioms("propext"), REG, ORACLE, ["checked_kill"])["ok"])
        self.assertFalse(mcprun.semantic_success([], REG, ORACLE, ["checked_kill"])["ok"])

    def test_wrapped_axiom_line(self):
        items = [dict(x, message=x["message"].replace(", ", ",\n ")) for x in axioms("propext", "Quot.sound")]
        self.assertTrue(mcprun.semantic_success(items, REG, ORACLE, ["checked_kill"])["ok"])

    def test_forbidden_axiom(self):
        self.assertFalse(mcprun.semantic_success(axioms("sorryAx"), REG, ORACLE, ["checked_kill"])["ok"])
        self.assertFalse(mcprun.semantic_success(axioms("Lean.ofReduceBool"), REG, ORACLE, ["checked_kill"])["ok"])

    def test_error_or_warning_fails(self):
        for sev in ("error", "warning"):
            self.assertFalse(mcprun.semantic_success(axioms() + [item(104, "x", sev)], REG, ORACLE, [])["ok"])

    def test_kill_must_state_unsoundness(self):
        self.assertFalse(mcprun.semantic_success(axioms(kill_sig="True"), REG, ORACLE, ["checked_kill"])["ok"])

    def test_target_warning_ignored_oracle_warning_fails(self):
        self.assertTrue(mcprun.semantic_success(axioms() + [item(50, "linter", "warning")], REG, ORACLE,
                                                ["checked_kill"])["ok"])
        self.assertFalse(mcprun.semantic_success(axioms() + [item(104, "linter", "warning")], REG, ORACLE,
                                                 ["checked_kill"])["ok"])

    def test_options_refused(self):
        with self.assertRaises(ValueError):
            mcprun.owned(ORACLE.replace("namespace H28.T", "set_option debug.skipKernelTC true\nnamespace H28.T"))
        mcprun.owned(ORACLE.replace("end H28.T", "set_option pp.fullNames true\nend H28.T"))

    def test_link_constructor(self):
        self.assertEqual(mcprun.link_constructor("theorem source_link : Taclet C 0 .box s p := .requireSimple"),
                         "Taclet.requireSimple")
        self.assertEqual(mcprun.link_constructor(
            "theorem source_link : ∀ b : Bool, LeanTaclet C 0 m (s b) (p b) := fun b => .transferDiamond"),
            "LeanTaclet.transferDiamond")

    def test_required_theorem(self):
        self.assertFalse(mcprun.semantic_success(axioms(), REG, ORACLE, ["missing"])["ok"])

    def test_trust_shortcuts_refused(self):
        with self.assertRaises(ValueError):
            mcprun.owned(ORACLE.replace("trivial\ntheorem checked_kill", "by sorry\ntheorem checked_kill"))
        with self.assertRaises(ValueError):
            mcprun.owned(ORACLE.replace("#print axioms checked_kill\n", ""))

    def test_rejection_must_be_at_source_link(self):
        link = REG["oracle"][0] + 1  # the source_link line of the stripped body
        ok = mcprun.source_link_rejection([item(link, "Type mismatch\n  Taclet.requireSimple")], REG, ORACLE)
        self.assertTrue(ok["ok"])
        multi = ORACLE.replace("theorem source_link : True := trivial", "theorem source_link : True :=\n  trivial")
        self.assertTrue(mcprun.source_link_rejection([item(link + 1, "Type mismatch\n  Taclet.c")], REG, multi)["ok"])
        self.assertFalse(mcprun.source_link_rejection([item(link + 2, "Type mismatch\n  Taclet.c")], REG, multi)["ok"])
        self.assertFalse(mcprun.source_link_rejection([item(link, "Type mismatch\n  Taclet.revertBox")], REG, ORACLE,
                                                      "Taclet.requireSimple")["ok"])
        for bad in ([item(link + 1, "Type mismatch Taclet.x")], [item(link, "unknown identifier")], [],
                    [item(50, "error in target"), item(link, "Type mismatch Taclet.x")]):
            self.assertFalse(mcprun.source_link_rejection(bad, REG, ORACLE)["ok"])


class Summary(unittest.TestCase):
    def test_unrun_never_scored(self):
        import json, tempfile, pathlib
        with tempfile.TemporaryDirectory() as d:
            out = pathlib.Path(d)
            (out / "checks").mkdir()
            m = {"proof_baselines": [{"id": "b"}], "mutants": [{"id": "x", "family": "f"}, {"id": "y", "family": "f"}],
                 "semantic_cases": [{"id": "s", "kind": "mutant", "family": "f"}]}
            (out / "checks/baseline.b.json").write_text(json.dumps({"result": {"outcome": "pass"}}))
            (out / "checks/proof.x.json").write_text(json.dumps({"result": {"outcome": "detected"}, "elapsed_s": 1}))
            s = mcprun.summarize(m, out)
            self.assertEqual(s["proof_oracle"]["census_counts"], {"detected": 1, "unrun": 1})
            self.assertEqual(s["mutants"]["y"]["outcome"], "unrun")
            self.assertEqual(s["semantic_witness_validation"]["denominator_killed_or_witness_failed"], 0)
            self.assertFalse(s["runner_cases_complete"])

    def semantic(self, mutant_result):
        import json, tempfile, pathlib
        with tempfile.TemporaryDirectory() as d:
            out = pathlib.Path(d)
            (out / "checks").mkdir()
            m = {"proof_baselines": [], "mutants": [],
                 "semantic_cases": [{"id": "s", "kind": "mutant", "family": "f", "constructor": "Taclet.c"}]}
            for ph, res in (("normal-oracle", {"ok": True}), ("normal-witness", {"ok": True, "link": "Taclet.c"}),
                            ("mutant-witness", mutant_result), ("mutant-oracle", {"outcome": "recorded"})):
                (out / f"checks/semantic.s.{ph}.json").write_text(json.dumps({"result": res}))
            return mcprun.summarize(m, out)["semantic"]["s"]["outcome"]

    def test_bridge_error_is_not_a_survivor(self):
        self.assertEqual(self.semantic({"outcome": "error", "reason": "bridge"}), "error")
        self.assertEqual(self.semantic({"ok": False, "witness_failed": False}), "error")
        self.assertEqual(self.semantic({"ok": False, "witness_failed": True}), "witness-failed")
        self.assertEqual(self.semantic({"ok": True}), "killed")

    def test_failed_baseline_voids_detection(self):
        import json, tempfile, pathlib
        with tempfile.TemporaryDirectory() as d:
            out = pathlib.Path(d)
            (out / "checks").mkdir()
            m = {"proof_baselines": [{"id": "b"}], "mutants": [{"id": "x", "family": "f"}]}
            (out / "checks/baseline.b.json").write_text(json.dumps({"result": {"outcome": "fail"}}))
            (out / "checks/proof.x.json").write_text(json.dumps({"result": {"outcome": "detected"}, "elapsed_s": 1}))
            self.assertEqual(mcprun.summarize(m, out)["mutants"]["x"]["outcome"], "error")


    def survivor(self, results, kind="sound-survivor", link="Taclet.c"):
        import json, tempfile, pathlib
        with tempfile.TemporaryDirectory() as d:
            out = pathlib.Path(d)
            (out / "checks").mkdir()
            m = {"proof_baselines": [], "mutants": [],
                 "semantic_cases": [{"id": "s", "kind": kind, "family": "f", "constructor": "Taclet.c"}]}
            base = {"normal-oracle": {"ok": True}, "normal-witness": {"ok": True, "link": link},
                    "mutant-witness": {"ok": True}, "mutant-oracle": {"outcome": "recorded"}}
            base.update(results)
            for ph, res in base.items():
                if res is not None:
                    (out / f"checks/semantic.s.{ph}.json").write_text(json.dumps({"result": res}))
            return mcprun.summarize(m, out)

    def test_sound_survivor_needs_every_phase(self):
        s = self.survivor({})
        self.assertEqual(s["semantic"]["s"]["outcome"], "survivor-sound")
        self.assertTrue(s["controls_pass"])
        # a survivor proof is never scored as a kill or a witness failure
        self.assertEqual(s["semantic_witness_validation"]["denominator_killed_or_witness_failed"], 0)
        self.assertEqual(self.survivor({"normal-witness": {"ok": False}})["semantic"]["s"]["outcome"], "error")
        self.assertEqual(self.survivor({"mutant-witness": {"ok": False, "witness_failed": True}})
                         ["semantic"]["s"]["outcome"], "error")
        self.assertEqual(self.survivor({"mutant-witness": None})["semantic"]["s"]["outcome"], "unrun")
        self.assertEqual(self.survivor({}, link="Taclet.other")["semantic"]["s"]["outcome"], "error")

    def test_sound_all_must_be_universal_soundness(self):
        oracle = ORACLE.replace("theorem source_link :", "theorem source_link_all :").replace(
            "#print axioms source_link\n", "#print axioms source_link_all\n").replace(
            "checked_kill", "sound_all")
        def run(sig):
            items = [item(107, "H28.T.sound_all : " + sig, "info")]
            for n in ("source_link_all", "sound_all"):
                items.append(item(105, f"'H28.T.{n}' does not depend on any axioms", "info"))
            return mcprun.semantic_success(items, REG, oracle, ["source_link_all", "sound_all"])["ok"]
        self.assertTrue(run("∀ {C : Solidity.Contract} (k : Nat) (σ : Solidity.State C Γ),\n  Solidity.Premise.Sound m s (H28.T.mutated k) σ"))
        self.assertFalse(run("∀ (σ : Solidity.State C Γ), ¬Solidity.Premise.Sound m s p σ"))
        self.assertFalse(run("Solidity.Premise.Sound m s p H28.T.start"))
        # parameters bound, but the state fixed: not universal
        self.assertFalse(run("∀ (k : Nat), Solidity.Premise.Sound m s p H28.T.start"))
        # a hypothesis restricting the state
        self.assertFalse(run("∀ (σ : Solidity.State C Γ), σ = σ → Solidity.Premise.Sound m s p σ"))
        self.assertFalse(run("True"))

    def test_semantic_control(self):
        link = REG["oracle"][0] + 1  # source_link line of the stripped body
        sc = mcprun.semantic_control
        # failure in the kill argument, after the link: the control passes
        ax = [item(105, "'H28.T.source_link' depends on axioms: [propext]", "info"),
              item(106, "'H28.T.checked_kill' depends on axioms: [propext, sorryAx]", "info")]
        self.assertTrue(sc([item(link + 2, "rfl failed")] + ax, REG, ORACLE)["ok"])
        # the failure must reach checked_kill, and the link must be clean
        self.assertFalse(sc([item(link + 2, "rfl failed")] + ax[:1] + [
            item(106, "'H28.T.checked_kill' depends on axioms: [propext]", "info")], REG, ORACLE)["ok"])
        self.assertFalse(sc([item(link + 2, "rfl failed")] + [
            item(105, "'H28.T.source_link' depends on axioms: [sorryAx]", "info")] + ax[1:], REG, ORACLE)["ok"])
        # an error before the link (a typo in a definition) is refused
        self.assertFalse(sc([item(link - 1, "unknown identifier")] + ax, REG, ORACLE)["ok"])
        # the link itself failing is not a semantic control
        self.assertFalse(sc([item(link, "Type mismatch Taclet.x")], REG, ORACLE)["ok"])
        # the target failing, a runtime limit: never ok
        self.assertFalse(sc([item(50, "x"), item(link + 2, "y")], REG, ORACLE)["ok"])
        self.assertFalse(sc([item(link + 2, "maximum recursion depth")], REG, ORACLE)["ok"])
        # no error: the kill went through (a production rule would be unsound)
        r = sc([], REG, ORACLE)
        self.assertFalse(r["ok"])
        self.assertTrue(r["killed"])
        s = self.survivor({"normal-witness": {"ok": True}}, kind="semantic-control")
        self.assertEqual(s["semantic"]["s"]["outcome"], "semantic-witness-failed")
        s = self.survivor({"normal-witness": {"ok": False, "killed": True}}, kind="semantic-control")
        self.assertEqual(s["semantic"]["s"]["outcome"], "killed")

    def test_negative_control_expectation(self):
        s = self.survivor({"mutant-witness": {"ok": False, "witness_failed": True}}, kind="negative-control")
        self.assertEqual(s["semantic"]["s"]["outcome"], "witness-failed")


if __name__ == "__main__":
    unittest.main()
