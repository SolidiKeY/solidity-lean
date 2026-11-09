"""Guard false witness credit from incomplete logs, stale categories and failed runs."""
import json
import unittest
import tempfile
import hashlib
from unittest.mock import patch
from pathlib import Path
from witness_results import reconcile, PREFIX, check_binding, audit_command


class WitnessResultsTests(unittest.TestCase):
    def setUp(self):
        self.rows = [dict(witness="N.w", target="Solidity.T", leading_binders=2,
                         prop_binders=1, kind="joint-premises", witness_axioms=[],
                         target_axioms=["propext"]),
                     dict(witness="N.v", target="Solidity.U", leading_binders=0,
                         prop_binders=0, kind="no-input-tuple", witness_axioms=[], target_axioms=[])]
        self.plan = dict(rows=self.rows, kernel_checked=False, historical_replay=False, meaning_checked=False)
        self.receipt = dict(exit=0, process_exit=0, resource_stop=False,
                            minimum_parent_headroom_bytes=4*1024**3,
                            limits=dict(memory_max=12*1024**3, memory_swap_max=0, lean_num_threads=1))

    def check_rows(self, rows):
        return reconcile(self.plan, "\n".join(PREFIX + json.dumps(r) for r in rows), self.receipt)

    def test_closed_schema_not_input_credit(self):
        result = self.check_rows(self.rows)
        self.assertEqual(result["input_tuple_certificates"], 1)
        self.assertEqual(result["kind_counts"], {"joint-premises": 1, "no-input-tuple": 1})
        self.assertFalse(result["receipt_authenticity_checked"])

    def test_missing_duplicate_and_extra_rows_refused(self):
        for rows in (self.rows[:1], self.rows + self.rows[:1],
                     self.rows + [dict(self.rows[0], witness="N.extra", target="Solidity.Extra")]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                self.check_rows(rows)

    def test_bad_counts_categories_and_axioms_refused(self):
        for update in (dict(leading_binders=True), dict(prop_binders=3),
                       dict(kind="inputs-without-premises"), dict(witness_axioms=["sorryAx"]),
                       dict(target_axioms=["PANIC"]), dict(target_axioms="propext")):
            with self.subTest(update=update), self.assertRaises(ValueError):
                self.check_rows([dict(self.rows[0], **update), self.rows[1]])

    def test_failure_stop_and_resources_refused(self):
        for update in (dict(exit=1), dict(process_exit=1), dict(resource_stop=True),
                       dict(minimum_parent_headroom_bytes=4*1024**3-1),
                       dict(limits=dict(memory_max=12*1024**3, memory_swap_max=1, lean_num_threads=1))):
            receipt = dict(self.receipt, **update)
            with self.subTest(update=update), self.assertRaises(ValueError):
                reconcile(self.plan, "", receipt)

    def test_malformed_and_embedded_records_refused(self):
        for log in (PREFIX + "{", "noise " + PREFIX + json.dumps(self.rows[0])):
            with self.assertRaises((ValueError, json.JSONDecodeError)):
                reconcile(self.plan, log, self.receipt)

    def test_command_stale_input_and_output_substitution_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "probe.lean"
            compiled = Path(tmp) / "compiled.json"
            compiled.write_text("{}")
            current = {"plan": "p", "sources": {"T.lean": "s"}}
            binding = dict(before=current, after=current, command=audit_command(path, compiled),
                           compiled_record=str(compiled),
                           compiled_sha256=hashlib.sha256(compiled.read_bytes()).hexdigest(),
                           log_sha256="log", receipt_sha256="receipt")
            receipt = dict(command=audit_command(path, compiled))
            with patch("witness_results.validate_build"):
                check_binding(binding, current, receipt, path, "log", "receipt")
                for update in (dict(before={}), dict(after={}), dict(command=["true"]),
                               dict(log_sha256="stale"), dict(receipt_sha256="stale"),
                               dict(compiled_sha256="stale")):
                    with self.subTest(update=update), self.assertRaises(ValueError):
                        check_binding(dict(binding, **update), current, receipt, path, "log", "receipt")
                with self.assertRaises(ValueError):
                    check_binding(binding, current, dict(command=["true"]), path, "log", "receipt")
            legacy = dict(binding)
            del legacy["compiled_record"]
            with self.assertRaises(ValueError):
                check_binding(legacy, current, receipt, path, "log", "receipt")

    def test_non_source_plan_refused(self):
        for field in ("kernel_checked", "historical_replay", "meaning_checked"):
            plan = dict(self.plan, **{field: True})
            with self.subTest(field=field), self.assertRaises(ValueError):
                reconcile(plan, "", self.receipt)


if __name__ == "__main__":
    unittest.main()
