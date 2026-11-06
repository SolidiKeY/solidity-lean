"""Scanner boundary acceptance; external tooling checks, not Lean proofs."""
import importlib.util
from pathlib import Path
import unittest
import json
import os
import subprocess
import sys
import tempfile
ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("census", ROOT / "scripts/h62/item4/generic-internalflow/census.py")
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)

class Boundaries(unittest.TestCase):
    def rows(self, source):
        return census.inventory("FixtureControls.lean", source)["declarations"]

    def test_comments_strings_and_nested_comments(self):
        source = '-- theorem ghost : False := by\n/- /- theorem ghost : False := by -/ -/\ndef text := "theorem ghost : False := by"\ntheorem real : True := by trivial\n'
        self.assertEqual([r["name"] for r in self.rows(source)], ["text", "real"])

    def test_result_lets_and_default_binder(self):
        source = 'theorem real (n : Nat := 1) :\n let x := n\n let y := x + 1\n y = n + 1 := by rfl\n'
        self.assertTrue(self.rows(source)[0]["header"].endswith('y = n + 1'))

    def test_equation_style(self):
        row = self.rows('def height : List Nat → Nat\n | [] => 0\n | _ :: xs => height xs\nend N\n')[0]
        self.assertEqual(row['header'], 'def height : List Nat → Nat')

    def test_guard_location(self):
        source = '\n/- comment -/\n\n#guard_msgs in\n#print axioms N.real\n'
        commands = census.inventory('Fixture.lean', source)['commands']
        self.assertEqual([r['line'] for r in commands], [4, 5])

    def test_review_regressions(self):
        cases = [('RuntimeFrameFootprint.lean', 'declare'), ('RuntimeFrameV3AllocatingScalarReturn.lean', 'return_turn')]
        for filename, name in cases:
            source = (ROOT / census.FAMILY / filename).read_text()
            row = next(r for r in self.rows(source) if r['name'] == name)
            self.assertIn('let ', row['header'])
            self.assertNotEqual(row['header'].split()[-1], 'next')
            start = source.index(row['header'])
            expected = source.index(':= by', start)
            self.assertEqual(row['header'], source[start:expected].strip())

class AcceptanceSafety(unittest.TestCase):
    def test_baseline_alias_refused_without_mutation(self):
        with tempfile.TemporaryDirectory() as directory:
            baseline = Path(directory) / "baseline.json"
            baseline.write_text('{"files": []}')
            original = baseline.read_bytes()
            alias = Path(directory) / "alias.json"
            alias.symlink_to(baseline)
            result = subprocess.run([sys.executable, spec.origin, "--output", str(alias), "--compare", str(baseline)], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(baseline.read_bytes(), original)
            self.assertIn(b"must not overwrite", result.stderr)

    def test_missing_build_target_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            # The builder version-checks this executable; no Lean is invoked.
            fake = Path(directory) / "lean"
            fake.write_text('#!/bin/sh\necho "Lean (version 4.35.0, test stub)"\n')
            fake.chmod(0o700)
            result = subprocess.run([sys.executable, str(Path(spec.origin).with_name("build.py")), "--lean", str(fake), "--output", directory, "H62.Nonexistent.Target"], capture_output=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b"requested source target missing", result.stderr)
            self.assertNotIn(b"PASS", result.stdout)

if __name__ == '__main__':
    unittest.main()
