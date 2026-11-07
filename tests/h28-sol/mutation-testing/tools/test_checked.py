"""Parser fixtures only; synthetic messages never establish semantic acceptance."""
import json
import unittest
import checked
import backend_controls

OK = {"kind": "exit", "exit": 0}
FAIL = {"kind": "exit", "exit": 1}
NAME = "H28.Example.checked_kill"


def msg(data, severity="information", file="Oracle.lean", line=12):
    return json.dumps({"data": data, "severity": severity, "fileName": file, "pos": {"line": line}}) + "\n"


def good():
    return msg("'" + NAME + "' depends on axioms: [propext]") + msg(NAME + " : True")


class CheckedControls(unittest.TestCase):
    def test_backend_infrastructure_error_cannot_pass_negative_controls(self):
        bad = {"kind": "error", "exit": 1, "source_unchanged": True}
        self.assertFalse(backend_controls.expected_outcome("forbidden-downstream-import", bad, "Taclet.olean' of module Solidity.Calculus.Taclet does not exist"))
        self.assertFalse(backend_controls.expected_outcome("readonly-source", bad, "read-only file system"))

    def test_backend_error_is_not_timeout_control(self):
        self.assertFalse(backend_controls.expected_outcome("timeout", {"kind": "error", "exit": None}, ""))

    def test_universal_at_signature(self):
        text = good().replace(NAME + " : True", "@" + NAME + " : ∀ n : Nat, n = n")
        self.assertIn("∀", checked.success(OK, text, [NAME])["signatures"][NAME])

    def test_all_owned_axioms_covers_unselected_helpers(self):
        source = "namespace H28.Example\ntheorem checked_kill : True := True.intro\ntheorem helper : True := True.intro\n#print axioms checked_kill\n#print axioms helper\nend H28.Example\n"
        text = good() + msg("'H28.Example.helper' depends on axioms: [propext]")
        self.assertEqual(len(checked.all_owned_axioms(OK, text, source)), 2)
        for bad in (text.replace("helper' depends on axioms: [propext]", "helper' depends on axioms: [Forged]"), good(), text + msg("'H28.Example.helper' depends on axioms: [propext]")):
            with self.assertRaises(ValueError): checked.all_owned_axioms(OK, bad, source)
        with self.assertRaises(ValueError): checked.all_owned_axioms(OK, text, source.replace("#print axioms helper\n", ""))
        with self.assertRaises(ValueError): checked.all_owned_axioms(OK, text, source.replace("theorem helper", "private theorem helper"))

    def test_oracle_comment_scanner_cannot_hide_declarations(self):
        hidden = 'def a : String := "/-"\ntheorem hidden : True := True.intro\ndef b : String := "-/"'
        with self.assertRaises(ValueError): checked.oracle_code(hidden)
        clean = checked.oracle_code("-- /-\naxiom forbidden : True\n-- -/\n")
        self.assertIn("axiom forbidden", clean)
        self.assertNotIn("theorem", checked.oracle_code("/- outer /- inner -/ theorem commentOnly -/"))
        with self.assertRaises(ValueError): checked.oracle_code("/- unterminated")
        with self.assertRaises(ValueError): checked.oracle_code("example : True := True.intro")
        with self.assertRaises(ValueError): checked.oracle_code("def «/-» := True")

    def test_valid_structure(self):
        self.assertEqual(checked.success(OK, good(), [NAME])["axioms"][NAME], ["propext"])

    def test_nonzero_never_success(self):
        for result in [FAIL, {"kind": "timeout", "exit": None}, {"kind": "error", "exit": 0}]:
            with self.assertRaises(ValueError): checked.success(result, good(), [NAME])

    def test_placeholder_rejected(self):
        with self.assertRaises(ValueError): checked.success(OK, good().replace("propext", "sorryAx"), [NAME])

    def test_unknown_axiom_rejected(self):
        with self.assertRaises(ValueError): checked.success(OK, good().replace("propext", "Fabricated"), [NAME])

    def test_missing_signature_rejected(self):
        with self.assertRaises(ValueError): checked.success(OK, good().splitlines()[0], [NAME])

    def test_duplicate_axioms_rejected(self):
        with self.assertRaises(ValueError): checked.success(OK, good() + good(), [NAME])

    def test_error_or_warning_rejected(self):
        for severity in ["warning", "error"]:
            with self.assertRaises(ValueError): checked.success(OK, good() + msg("bad", severity), [NAME])

    def test_non_json_failure_rejected(self):
        with self.assertRaises(ValueError): checked.success(OK, good() + "compiler crashed", [NAME])

    def test_attributed_source_rejection(self):
        text = msg("Type mismatch\nTaclet.requireSimple", "error")
        self.assertEqual(checked.source_link_rejection(FAIL, text, "Oracle.lean", 12)["line"], 12)
        for result, file, line in [(OK, "Oracle.lean", 12), (FAIL, "Other.lean", 12), (FAIL, "Oracle.lean", 13)]:
            with self.assertRaises(ValueError): checked.source_link_rejection(result, text, file, line)

    def test_extra_errors_rejected(self):
        text = msg("Type mismatch\nTaclet.requireSimple", "error")
        with self.assertRaises(ValueError): checked.source_link_rejection(FAIL, text + text, "Oracle.lean", 12)

    def test_unrelated_failure_rejected(self):
        with self.assertRaises(ValueError): checked.source_link_rejection(FAIL, msg("unknown identifier", "error"), "Oracle.lean", 12)


if __name__ == "__main__": unittest.main(verbosity=2)
