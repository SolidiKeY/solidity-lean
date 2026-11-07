"""Missing key-rule inputs must fail before build artifacts or Lean jobs start."""
import pathlib, subprocess, sys, tempfile, unittest
sys.dont_write_bytecode = True
repo = pathlib.Path(__file__).resolve().parents[4]

class KeyRulesArgument(unittest.TestCase):
    def test_missing_and_nonexistent_rules_fail_before_writes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            command = [sys.executable, str(repo/'scripts/h62/item6/migrate-yul/build.py'),
                '--root', str(root/'repo'), '--toolchain', str(root/'tool'),
                '--artifacts', str(root/'artifacts'), '--census', str(root/'census.json'),
                '--label', 'control', '--kind', 'key']
            for suffix in [[], ['--key-rules', str(root/'missing.key')]]:
                run = subprocess.run(command+suffix, capture_output=True, text=True)
                self.assertEqual(run.returncode, 2)
                self.assertIn('--kind key requires --key-rules', run.stderr)
                self.assertFalse((root/'artifacts').exists())

if __name__ == '__main__':
    unittest.main()
