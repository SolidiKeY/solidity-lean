"""Parser rejection tests; actual proof acceptance requires run_controls.py."""
import unittest
from run_controls import check_log

class DiagnosticTests(unittest.TestCase):
    source = "theorem rejected : False := by\n  fail\n#h28_codegen_outer\n"
    def test_unrelated_setup_error_fails(self):
        self.assertFalse(check_log(self.source, "x.lean:1:0: error: Imports are out of date", 1, "sol_chain:", False)["passed"])
    def test_timeout_cannot_pass(self):
        self.assertIn("timeout or unexpected exit", check_log(self.source, "", 0, None, True, True)["errors"])
    def test_exit_zero_without_proof_or_audits_fails(self):
        self.assertIn("positive proof/diagnostic failure", check_log(self.source, "", 0, None, False)["errors"])
    def test_arbitrary_exit_one_fails(self):
        self.assertFalse(check_log(self.source, "", 1, "sol_chain:", False)["passed"])
    def test_wrong_error_class_fails(self):
        self.assertIn("wrong refusal class/location/count", check_log(self.source, "x.lean:2:0: error: type mismatch", 1, "sol_chain:", False)["errors"])

    def test_nonstandard_axiom_fails_even_when_print_matches(self):
        log = 'H28_AUDIT {"name":"prelude","axioms":[{"name":"Bad.ax","signature":"parser-only"}]}\nH28_REPLAY prelude\n' + "'prelude' depends on axioms: [Bad.ax]\n"
        self.assertIn("nonstandard axiom", check_log("#h28_audit prelude\n", log, 0, None, True)["errors"])
    def test_matching_error_in_another_file_fails(self):
        log = "other.lean:2:0: error: sol_chain: no rule applies to\n" * 2
        self.assertIn("wrong refusal class/location/count", check_log(self.source, log, 1, "sol_chain: no rule applies to", False, source_path="tested.lean")["errors"])
    def test_zero_step_extra_text_fails(self):
        reason = "sol_prove: steps must be between 1 and 20000"
        log = ("tested.lean:2:0: error: " + reason + " unexpected suffix\n") * 2
        self.assertIn("wrong refusal class/location/count", check_log(self.source, log, 1, reason, False, source_path="tested.lean")["errors"])
