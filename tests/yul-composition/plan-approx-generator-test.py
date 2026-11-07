"""Fail-closed provenance controls for the proof generator (no Lean execution)."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / 'scripts/yul-composition/generate-plan-approx.py'

class Provenance(unittest.TestCase):
    script = SCRIPT
    basis_path = 'Solidity/Source/Horizon.lean'
    output_path = 'Solidity/Source/FailureEvaluatorApprox.lean'

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.cwd = Path(self.temp.name)
        basis = self.cwd / self.basis_path
        basis.parent.mkdir(parents=True)
        basis.write_bytes((ROOT / self.basis_path).read_bytes())
        self.basis = basis
        self.output = self.cwd / 'proof.lean'
        self.run_script()

    def run_script(self, *args, expected=0):
        result = subprocess.run(['python3', str(self.script), '--output', str(self.output), *args],
            cwd=self.cwd, capture_output=True, text=True)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result

    def test_exact_current_proof(self):
        self.run_script('--check')
        self.assertEqual(self.output.read_bytes(),
            (ROOT / self.output_path).read_bytes())

    def test_disabled_plan_cannot_replace_fixed_plan(self):
        old = self.output.read_bytes()
        self.assertIn(b'plan := some points', old)
        self.output.write_bytes(old.replace(b'plan := some points', b'plan := none', 1))
        self.run_script('--check', expected=1)

    def test_missing_output_rejected(self):
        self.output.unlink()
        self.run_script('--check', expected=1)

    def test_changed_basis_rejected(self):
        self.basis.write_bytes(self.basis.read_bytes() + b'\n-- changed proof basis\n')
        self.run_script('--check', expected=1)

    def test_changed_line_endings_rejected(self):
        self.output.write_bytes(self.output.read_bytes().replace(b'\n', b'\r\n'))
        self.run_script('--check', expected=1)

class DeploymentProvenance(Provenance):
    script = ROOT / 'scripts/yul-composition/generate-plan-deploy.py'
    basis_path = 'Solidity/Source/HorizonDeploy.lean'
    output_path = 'Solidity/Source/FailureDeploymentHorizon.lean'

if __name__ == '__main__':
    unittest.main()
