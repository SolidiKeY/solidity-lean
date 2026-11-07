"""Pure policy controls only; flags here do not stand in for Lean proof runs."""
import copy
from pathlib import Path
import unittest
from unittest.mock import patch
import subprocess
import tempfile
import bounded
import backend_controls
import engine
import runner


class EnginePolicyControls(unittest.TestCase):
    def test_case_ids_cannot_be_directory_aliases(self):
        for name in (".", "..", "", "../x", "/x", "a/b"):
            self.assertFalse(engine.valid_id(name))
        self.assertTrue(engine.valid_id("control.guard-label-equivalent"))

    def test_cleanup_daemon_error_is_not_confirmed_absence(self):
        with patch("bounded.subprocess.run", return_value=subprocess.CompletedProcess([], 1, "", "Cannot connect to daemon")):
            self.assertFalse(bounded.remove_owned("owned", {}))

    def test_cleanup_live_container_is_not_confirmed_absence(self):
        with patch("bounded.subprocess.run", return_value=subprocess.CompletedProcess([], 0, "[]", "")):
            self.assertFalse(bounded.remove_owned("owned", {}))

    def test_cleanup_requires_no_such_object(self):
        with patch("bounded.subprocess.run", return_value=subprocess.CompletedProcess([], 1, "", "Error: No such object: owned")):
            self.assertTrue(bounded.remove_owned("owned", {}))

    def test_cleanup_timeout_is_not_success(self):
        with patch("bounded.subprocess.run", side_effect=subprocess.TimeoutExpired("docker", 15)):
            self.assertFalse(bounded.remove_owned("owned", {}))

    def test_clean_inactive_cache_is_available_but_not_unused(self):
        result = bounded.available_memory(16, 9, 17, {"inactive_file": 7, "file_dirty": 0, "file_writeback": 0})
        self.assertEqual(result["strict_unallocated_before"], 7)
        self.assertEqual(result["available_before"], 14)

    def test_dirty_pages_cannot_expand_headroom(self):
        result = bounded.available_memory(16, 9, 17, {"inactive_file": 7, "file_dirty": 6, "file_writeback": 1})
        self.assertEqual(result["reclaimable_clean_before"], 0)
        self.assertEqual(result["available_before"], 7)

    def test_os_available_caps_cgroup_estimate(self):
        result = bounded.available_memory(16, 9, 3, {"inactive_file": 7, "file_dirty": 0, "file_writeback": 0})
        self.assertEqual(result["available_before"], 3)

    def test_reclaimable_cannot_exceed_current(self):
        result = bounded.available_memory(16, 9, 100, {"inactive_file": 100, "file_dirty": 0, "file_writeback": 0})
        self.assertEqual(result["available_before"], 16)

    def test_unlimited_cgroup_does_not_double_count_cache(self):
        result = bounded.available_memory(None, 9, 5, {"inactive_file": 7, "file_dirty": 0, "file_writeback": 0})
        self.assertEqual(result["available_before"], 5)

    def test_missing_reclaim_counters_credit_nothing(self):
        self.assertEqual(bounded.available_memory(16, 9, 17, {"inactive_file": 7})["reclaimable_clean_before"], 0)

    def test_negative_reclaim_counter_refused(self):
        with self.assertRaises(ValueError): bounded.available_memory(16, 9, 17, {"inactive_file": -1})

    def test_partial_backend_controls_are_not_a_passing_gate(self):
        result = backend_controls.control_summary([{"label": "a", "passed": True}], ["a", "b"])
        self.assertFalse(result["pass"])
        self.assertEqual(result["unrun"], ["b"])

    def test_real_git_input_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            def git(*args):
                subprocess.run(["git", "-c", "user.name=H28 test", "-c", "user.email=h28@example.invalid", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args], cwd=repo, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            git("init", "-q")
            path = repo / "input.json"
            path.write_text("committed")
            git("add", "input.json")
            git("commit", "-qm", "provenance fixture")
            self.assertEqual(engine.committed_source(repo, path), b"committed")
            path.write_text("changed")
            with self.assertRaises(ValueError): engine.committed_source(repo, path)
            ignored = repo / "ignored.json"
            ignored.write_text("not committed")
            (repo / ".gitignore").write_text("ignored.json\n")
            with self.assertRaises(ValueError): engine.committed_source(repo, ignored)

    def test_authorized_delivery_base_does_not_allow_new_out_of_scope_edits(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            def git(*args):
                return subprocess.check_output(["git", "-c", "user.name=H28 fixture", "-c", "user.email=h28@example.invalid", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args], cwd=repo, stderr=subprocess.DEVNULL, text=True).strip()
            git("init", "-q")
            prod = repo / "production.lean"
            prod.write_text("original fixture")
            git("add", "."); git("commit", "-qm", "original fixture")
            original = git("rev-parse", "HEAD")
            prod.write_text("authorized upstream fixture")
            git("add", "."); git("commit", "-qm", "authorized fixture")
            authorized = git("rev-parse", "HEAD")
            owned = repo / "tests/h28-sol/mutation-testing/fixture.json"
            owned.parent.mkdir(parents=True)
            owned.write_text("owned fixture")
            git("add", "."); git("commit", "-qm", "owned fixture")
            owned_head = git("rev-parse", "HEAD")
            with patch("engine.BASE", original), patch("engine.DELIVERY_BASE", authorized):
                engine.validate_write_scope(repo)
                prod.write_text("unauthorized lane fixture")
                git("add", "."); git("commit", "-qm", "out of scope fixture")
                with self.assertRaises(ValueError): engine.validate_write_scope(repo)
                git("checkout", "--detach", owned_head)
                git("mv", "production.lean", "tests/h28-sol/mutation-testing/moved.lean")
                git("commit", "-qm", "producer rename fixture")
                unsafe = git("-c", "diff.renames=true", "diff", "--name-only", authorized, "HEAD").splitlines()
                self.assertNotIn("production.lean", unsafe)
                with self.assertRaises(ValueError): engine.validate_write_scope(repo)
                git("checkout", "--detach", original)
                with self.assertRaises(subprocess.CalledProcessError): engine.validate_write_scope(repo)

    def test_memory_profile_never_reduces_reserve_or_raises_maximum(self):
        gib = 1024**3
        self.assertEqual(bounded.choose_limit(10 * gib), 6 * gib)
        self.assertEqual(bounded.choose_limit(8 * gib), 4 * gib)
        self.assertEqual(bounded.choose_limit(6 * gib), 2 * gib)
        self.assertIsNone(bounded.choose_limit(6 * gib - 1))
        for available in range(0, 18):
            limit = bounded.choose_limit(available * gib)
            if limit is not None:
                self.assertLessEqual(limit, bounded.LIMIT)
                self.assertGreaterEqual(available * gib - limit, bounded.RESERVE)

    def setup_records(self):
        cases = [{"id": "m", "kind": "mutant"}, {"id": "k", "kind": "known-kill"}, {"id": "e", "kind": "equivalent-control"}]
        records = [dict(c, status="killed", baseline_passed=True, witness_verified=True) for c in cases]
        records[-1].update(status="equivalent", equivalence_verified=True)
        return cases, records

    def test_complete_pilot_is_not_scope_acceptance(self):
        cases, records = self.setup_records()
        result = engine.summarize(records, cases)
        self.assertTrue(result["runner_cases_complete"])
        self.assertFalse(result["scope_complete"])
        self.assertEqual(result["denominator_ids"], ["m"])
        self.assertEqual(result["score"], 1.0)

    def test_failed_equivalence_control_suppresses_score(self):
        cases, records = self.setup_records()
        records[-1].update(status="invalid-compilation", invalid_compilation_verified=True)
        result = engine.summarize(records, cases)
        self.assertIsNone(result["score"])
        self.assertFalse(result["runner_cases_complete"])

    def test_kill_without_witness_is_not_scored(self):
        cases, records = self.setup_records()
        records[0]["witness_verified"] = False
        result = engine.summarize(records, cases)
        self.assertEqual(result["denominator"], 0)
        self.assertIsNone(result["score"])
        self.assertFalse(result["runner_cases_complete"])

    def test_unverified_equivalence_cannot_pass(self):
        cases, records = self.setup_records()
        records[-1]["equivalence_verified"] = False
        self.assertFalse(engine.summarize(records, cases)["runner_cases_complete"])

    def test_known_kill_requires_baseline(self):
        cases, records = self.setup_records()
        records[1]["baseline_passed"] = False
        self.assertFalse(engine.summarize(records, cases)["known_kill_controls_pass"])

    def test_unrun_excluded_and_no_score(self):
        cases, records = self.setup_records()
        records = records[1:]
        result = engine.summarize(records, cases)
        self.assertEqual(result["unrun"], ["m"])
        self.assertEqual(result["denominator"], 0)
        self.assertIsNone(result["score"])

    def test_timeout_is_not_scored(self):
        cases, records = self.setup_records()
        records[0]["status"] = "timeout"
        result = engine.summarize(records, cases)
        self.assertEqual(result["denominator"], 0)
        self.assertIsNone(result["score"])

    def test_survivor_stays_visible_with_regression(self):
        cases, records = self.setup_records()
        records[0].update(status="surviving", regression_verified=True)
        result = engine.summarize(records, cases)
        self.assertEqual(result["denominator"], 1)
        self.assertEqual(result["killed"], 0)
        self.assertEqual(result["score"], 0.0)
        self.assertEqual(records[0]["status"], "surviving")

    def test_survivor_without_regression_blocks_completion(self):
        cases, records = self.setup_records()
        records[0]["status"] = "surviving"
        result = engine.summarize(records, cases)
        self.assertFalse(result["runner_cases_complete"])
        self.assertIsNone(result["score"])

    def test_unverified_invalid_compilation_blocks_completion(self):
        cases, records = self.setup_records()
        records[0]["status"] = "invalid-compilation"
        self.assertFalse(engine.summarize(records, cases)["runner_cases_complete"])

    def test_duplicate_and_undeclared_results_refused(self):
        cases, records = self.setup_records()
        for extra in (copy.deepcopy(records[0]), {"id": "unknown", "status": "killed"}):
            with self.assertRaises(ValueError): engine.summarize(records + [extra], cases)

    def test_transitive_cache_pruning(self):
        graph = {"Rules": set(), "Taclet": {"Rules", "Independent"}, "Callback": {"Taclet"}, "Independent": set()}
        self.assertEqual(engine.forbidden_modules(graph, "Rules"), {"Rules", "Taclet", "Callback"})

    def test_rejection_without_witness_is_error(self):
        self.assertEqual(engine.primary_outcome(True, False), "error")

    def test_weak_primary_oracle_is_not_relabelled_by_witness(self):
        self.assertEqual(engine.primary_outcome(False, True), "surviving")
        self.assertEqual(engine.primary_outcome(True, True), "killed")

    def test_equivalence_conflict_is_error(self):
        self.assertEqual(engine.primary_outcome(True, True, True), "error")
        self.assertEqual(engine.primary_outcome(False, False, True), "equivalent")

    def test_artifact_retention_refuses_failed_compile_residue_and_overwrites(self):
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp) / "tree"
            evidence = Path(tmp) / "evidence"
            source = "Owned/Proof.lean"
            (tree / source).parent.mkdir(parents=True)
            (tree / source).write_text("theorem p : True := True.intro")
            artifact = tree / engine.artifact_path(source)
            artifact.parent.mkdir(parents=True)
            with self.assertRaises(ValueError): engine.retain_artifact(tree, source, evidence, "baseline-oracle")
            artifact.touch()
            with self.assertRaises(ValueError): engine.retain_artifact(tree, source, evidence, "baseline-oracle")
            artifact.unlink()
            artifact.symlink_to(tree / source)
            with self.assertRaises(ValueError): engine.retain_artifact(tree, source, evidence, "baseline-oracle")
            artifact.unlink()
            artifact.write_bytes(b"test fixture, not a real Lean proof")
            normal = engine.retain_artifact(tree, source, evidence, "baseline-oracle")
            changed = engine.retain_artifact(tree, source, evidence, "mutant-witness")
            self.assertNotEqual(normal["path"], changed["path"])
            self.assertEqual(normal["sha256"], changed["sha256"])
            with self.assertRaises(ValueError): engine.retain_artifact(tree, source, evidence, "baseline-oracle")

    def test_manifest_path_must_be_committed(self):
        with self.assertRaises(ValueError): runner.run(Path("."), {"schema": 2, "state": "frozen"}, Path("unused"))


if __name__ == "__main__": unittest.main(verbosity=2)
