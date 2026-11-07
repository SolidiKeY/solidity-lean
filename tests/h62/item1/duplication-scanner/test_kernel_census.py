"""Guard generated-row omission, name collisions and saved-census promotion."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[4]
SCRIPTS = ROOT / "scripts/h62/item1/duplication-scanner"
sys.path.insert(0, str(SCRIPTS))
try:
    spec = importlib.util.spec_from_file_location("kernel_census", SCRIPTS / "census_fixture_kernel.py")
    census = importlib.util.module_from_spec(spec); spec.loader.exec_module(census)
finally:
    sys.path.pop(0)


def name(part):
    return ["str", ["anonymous"], part]


def packet():
    return {"format": 1, "module": census.MODULE, "total": 2,
            "rows": [{"declaration": name("generated.rec"), "kind": "recursor", "status": "serialized", "signature": []},
                     {"declaration": name("unsupported"), "kind": "definition", "status": "unsupported", "reason": "expression metadata"}]}


class KernelCensusControls(unittest.TestCase):
    def test_unsupported_and_generated_rows_are_retained(self):
        value = packet(); result = census.validate(value)
        self.assertEqual(result["rows"], value["rows"])
        self.assertEqual([row["status"] for row in result["rows"]], ["serialized", "unsupported"])

    def test_missing_row_cannot_pass_reported_total(self):
        value = packet(); value["rows"].pop()
        with self.assertRaisesRegex(ValueError, "count mismatch"): census.validate(value)

    def test_duplicate_generated_name_rejected_even_if_total_matches(self):
        value = packet(); value["rows"][1]["declaration"] = copy.deepcopy(value["rows"][0]["declaration"])
        with self.assertRaisesRegex(ValueError, "duplicate"): census.validate(value)

    def test_numeric_string_and_nested_same_spelling_names_remain_distinct(self):
        a = ["str", name("A"), "1"]; b = ["num", name("A"), 1]
        c = name("A.1")
        self.assertEqual(len({census.name_key(a), census.name_key(b), census.name_key(c)}), 3)
        value = packet(); value["rows"][0]["declaration"] = a; value["rows"][1]["declaration"] = b
        self.assertEqual(census.validate(value)["total"], 2)

    def test_empty_or_forged_status_does_not_hide_type_refusal(self):
        for mutate in (lambda r:r.update(reason=""), lambda r:r.pop("reason"), lambda r:r.update(status="proved")):
            value = packet(); mutate(value["rows"][1])
            with self.assertRaises(ValueError): census.validate(value)

    def test_late_error_or_duplicate_key_in_log_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "probe.log"
            text = census.observer.PREFIX+'{}\n'+census.PREFIX+json.dumps(packet())+'\n'
            log.write_text(text+'error: late failure\n')
            with self.assertRaisesRegex(ValueError, "unexpected census log"): census.read_log(log)
            log.write_text(census.observer.PREFIX+'{}\n'+census.PREFIX+'{"format":1,"format":1}\n')
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"): census.read_log(log)

    def test_saved_success_packet_never_triggers_rebuild_or_promotion(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "existing"; output.mkdir()
            (output / "receipt.json").write_text('{"status":"pass"}')
            with mock.patch.object(census, "rebuild") as rebuild:
                with self.assertRaises(FileExistsError): census.run(output)
            rebuild.assert_not_called()

    def test_self_consistent_generated_omission_fails_fixture_acceptance(self):
        value = packet()
        # Even a structurally consistent packet cannot replace the generated-control gate.
        with self.assertRaisesRegex(ValueError, "required generated fixture constant"):
            census.verify_fixture_controls(census.validate(value), [])

    def test_structural_validator_alone_does_not_authenticate_completeness(self):
        value = packet(); value["rows"].pop(); value["total"] = 1
        self.assertEqual(census.validate(value)["total"], 1)
        # The CLI exposes no saved-census input path: only trusted live execution can pass.
        result = subprocess.run([sys.executable, "-B", str(SCRIPTS / "census_fixture_kernel.py"),
                                 "--output", "/unused", "--receipt", "/forged"], capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b"unrecognized arguments", result.stderr)


if __name__ == "__main__": unittest.main()
