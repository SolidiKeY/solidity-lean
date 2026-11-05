"""Negative controls for draft runner false passes; no Lean is invoked."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("h28_runner", Path(__file__).with_name("runner.py"))
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)
OK = {"kind": "exit", "exit": 0}
FAIL = {"kind": "exit", "exit": 1}
LINE = "Witness.lean:10:2: error: unsolved goals"
PATTERN = r"Witness\.lean:10:2: error: unsolved goals"


class RunnerControls(unittest.TestCase):
    def test_no_arbitrary_exit_kill(self):
        for code in (-9, 2, 137):
            self.assertEqual(r.classify(OK, {"kind": "exit", "exit": code}, LINE, [PATTERN]), "error")

    def test_mixed_infrastructure_failures(self):
        for extra in ("Killed", "compiler crashed: out of memory", "timeout", "panic"):
            self.assertEqual(r.classify(OK, FAIL, LINE + "\n" + extra, [PATTERN]), "error")

    def test_missing_required_diagnostic(self):
        self.assertEqual(r.classify(OK, FAIL, LINE, [PATTERN, "another error"]), "error")

    def test_unexpected_diagnostic(self):
        self.assertEqual(r.classify(OK, FAIL, LINE + "\nOther.lean:1:1: error: unknown identifier", [PATTERN]), "error")

    def test_duplicate_diagnostic(self):
        self.assertEqual(r.classify(OK, FAIL, LINE + "\n" + LINE, [PATTERN]), "error")

    def test_proof_rejection_is_not_semantic_kill(self):
        self.assertEqual(r.classify(OK, FAIL, LINE, [PATTERN]), "oracle-rejected-unvalidated")

    def test_compile_resource_failure_is_not_invalid_mutant(self):
        for code in (-9, 2, 137):
            self.assertEqual(r.classify({"kind": "exit", "exit": code}, None, "", []), "error")

    def test_status_separation(self):
        self.assertEqual(r.classify(FAIL, None, "", []), "invalid-compilation")
        self.assertEqual(r.classify({"kind": "timeout", "exit": None}, None, "", []), "timeout")
        self.assertEqual(r.classify(OK, None, "", []), "unrun")
        self.assertEqual(r.classify(OK, OK, "", []), "surviving")
        self.assertEqual(r.classify(OK, FAIL, "", []), "error")

    def test_unrun_not_scored(self):
        cases = [{"id": "m", "kind": "mutant"}, {"id": "c", "kind": "known-kill"}]
        result = r.summary([], cases)
        self.assertEqual(result["denominator"], 0)
        self.assertIsNone(result["score"])
        self.assertEqual(result["unrun"], ["m", "c"])
        self.assertFalse(result["scope_complete"])

    def test_runner_completion_is_not_scope_completion(self):
        cases = [{"id": "m", "kind": "mutant"}, {"id": "c", "kind": "known-kill"}]
        records = [dict(c, status="killed") for c in cases]
        self.assertFalse(r.summary(records, cases)["scope_complete"])

    def test_unique_one_change_and_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "target").write_text("before\n")
            case = {"target": "target", "target_sha256": r.digest(b"before\n"),
                    "old": "before", "new": "after"}
            result = r.mutate(tree, case)
            self.assertEqual((tree / "target").read_text(), "after\n")
            self.assertEqual(result["after_sha256"], r.digest(b"after\n"))
            with self.assertRaises(ValueError):
                r.mutate(tree, case)

    def test_duplicate_span_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "target").write_text("x x")
            with self.assertRaises(ValueError):
                r.mutate(tree, {"target": "target", "target_sha256": r.digest(b"x x"), "old": "x", "new": "y"})

    def test_path_escape_refused(self):
        for path in ("/etc/passwd", "../x", "a/../../x"):
            with self.assertRaises(ValueError):
                r.relative(path)

    def test_unfrozen_execution_refused(self):
        with self.assertRaises(ValueError):
            r.run(Path("."), {}, Path("unused"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
