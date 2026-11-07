"""Guard source-plan ordering, comment confusion and fail-closed source pins."""
import importlib.util, os, pathlib, subprocess, tempfile, unittest

SCRIPT = pathlib.Path(__file__).with_name('serial-build.py')
spec = importlib.util.spec_from_file_location('serial_build', SCRIPT)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

class PlanControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name)
        self.previous_inputs = m.execution_inputs
        m.execution_inputs = lambda: []
        self.addCleanup(setattr, m, 'execution_inputs', self.previous_inputs)
        self.previous = m.ROOT
        m.ROOT = self.root
        self.addCleanup(setattr, m, 'ROOT', self.previous)
        self.env = dict(os.environ, GIT_AUTHOR_NAME='Control', GIT_AUTHOR_EMAIL='control@example.invalid',
                        GIT_COMMITTER_NAME='Control', GIT_COMMITTER_EMAIL='control@example.invalid')
        self.git('init', '-q')
    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.root), *args], env=self.env)
    def source(self, name, text):
        p = self.root / (name.replace('.', '/') + '.lean')
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    def commit(self):
        self.git('add', '.')
        self.git('commit', '-qm', 'fixture')
    def test_order_and_nested_comment_prose(self):
        self.source(m.TARGET, '/- outer /- nested -/ -/\nimport\tSolidity.Leaf -- trailing\n/-!\nimport prose is not an import\n-/\ndef x := 1\n')
        self.source('Solidity.Leaf', 'def leaf := 1\n')
        self.commit()
        self.assertEqual([e['module'] for e in m.prepare()['entries']], ['Solidity.Leaf', m.TARGET])
    def test_uncommitted_source_and_missing_import_fail(self):
        self.source(m.TARGET, 'def x := 1\n')
        self.commit()
        self.source(m.TARGET, 'def x := 2\n')
        with self.assertRaisesRegex(ValueError, 'differs from HEAD'):
            m.prepare()
        self.source(m.TARGET, 'import Solidity.Missing\n')
        self.commit()
        with self.assertRaises(FileNotFoundError):
            m.prepare()
    def test_cycles_and_unsupported_headers_fail(self):
        self.source(m.TARGET, 'import Solidity.Leaf\n')
        self.source('Solidity.Leaf', 'import '+m.TARGET+'\n')
        self.commit()
        with self.assertRaisesRegex(ValueError, 'cycle'):
            m.prepare()
        self.source(m.TARGET, 'import "unexpected"\n')
        self.commit()
        with self.assertRaisesRegex(ValueError, 'unsupported import'):
            m.prepare()

    def test_prelude_and_public_import_fail(self):
        for header in ['prelude', 'public import Solidity.Leaf']:
            self.source(m.TARGET, header+'\n')
            self.commit()
            with self.assertRaisesRegex(ValueError, 'unsupported import header'):
                m.prepare()

if __name__ == '__main__':
    unittest.main()
