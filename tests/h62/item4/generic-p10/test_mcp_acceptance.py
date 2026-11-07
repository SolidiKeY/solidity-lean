"""Regress the observed transport-success/Lean-failure distinction."""
import json
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'scripts/h62/item4/generic-p10'))
from accept_semantics import require_success


class MCPAcceptanceTests(unittest.TestCase):
    def test_actual_failed_lean_report_is_refused_despite_cli_exit0(self):
        report=json.loads((ROOT.parent/'generic-p10-artifacts/evidence/resume-owner-validation.json').read_text())
        self.assertIs(report['success'],False)
        with self.assertRaises(ValueError):require_success(report)

    def test_actual_corrected_lean_report_is_accepted(self):
        report=json.loads((ROOT.parent/'generic-p10-artifacts/evidence/resume-owner-validation-fixed.json').read_text())
        require_success(report)

    def test_partial_or_untyped_success_is_not_acceptance(self):
        with self.assertRaises(ValueError):require_success(dict(success=True))
        with self.assertRaises(ValueError):require_success(dict(success=True,partial=True,timed_out=False,items=[]),True)

    def test_missing_diagnostic_payload_is_refused(self):
        with self.assertRaises(ValueError):require_success(dict(success=True,partial=False,timed_out=False,failed_dependencies=[]),True)
        with self.assertRaises(ValueError):require_success(dict(success=True,timed_out=False))
        with self.assertRaises(ValueError):require_success([])
        with self.assertRaises(ValueError):require_success(dict(success=True,timed_out=False,diagnostics=[{}]))

    def test_real_complete_diagnostic_and_build_shapes_are_accepted(self):
        evidence=ROOT.parent/'generic-p10-artifacts/evidence'
        require_success(json.loads((evidence/'resume-fixture-axioms.json').read_text()),True)
        require_success(json.loads((evidence/'resume-full-affected-build.json').read_text()),build=True)


if __name__=='__main__':unittest.main()
