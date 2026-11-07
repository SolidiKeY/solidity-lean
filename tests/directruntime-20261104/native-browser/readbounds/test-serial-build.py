"""Guard source-plan ordering, comment confusion and fail-closed source pins."""
import contextlib, importlib.util, io, json, os, pathlib, shlex, subprocess, sys, tempfile, unittest
from unittest import mock

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

    def runtime_fixture(self,mutation=None):
        self.source(m.TARGET,'def fixture := 1\n');self.commit()
        runtime=self.root/'runtime-input';runtime.write_text('pinned')
        fake=self.root/'fixture-lake'
        text='#!/bin/sh\nprintf "fixture-only: no Lean executed\\n"\n'
        if mutation is not None:text+='printf mutated > '+shlex.quote(str(mutation(runtime)))+'\n'
        fake.write_text(text);fake.chmod(0o755)
        m.execution_inputs=lambda:[{'path':str(p),'sha256':m.sha(p.read_bytes())} for p in (fake,runtime)]
        plan=m.prepare();path=self.root/'plan.json';path.write_text(json.dumps(plan))
        run=self.root/'run'
        return fake,path,run

    def run_fixture(self,fake,path,run):
        with mock.patch.object(m,'LAKE',fake),mock.patch.object(sys,'argv',['serial-build',str(path),'--run',str(run),'--expected-sha256',m.sha(path.read_bytes())]),mock.patch.dict(os.environ,{'LEAN_NUM_THREADS':'1'}),contextlib.redirect_stdout(io.StringIO()):
            m.main()

    def test_execution_uses_real_small_fixture_command_not_lean(self):
        fake,path,run=self.runtime_fixture();self.run_fixture(fake,path,run)
        row=json.loads((run/'targets.jsonl').read_text())
        self.assertEqual(row['exit'],0);self.assertEqual(row['processExit'],0)
        self.assertIn('fixture-only',(run/'0.log').read_text())

    def test_zero_exit_overrun_propagates_failed_target(self):
        fake,path,run=self.runtime_fixture()
        # Synthetic clock jump tests deadline classification, not proof timing.
        with mock.patch.object(m.time,'monotonic_ns',side_effect=[0,301_000_000_000]):
            with self.assertRaises(SystemExit) as error:self.run_fixture(fake,path,run)
        self.assertEqual(error.exception.code,124)
        row=json.loads((run/'targets.jsonl').read_text())
        self.assertEqual(row['processExit'],0);self.assertEqual(row['exit'],124)

    def test_execution_input_mutation_after_zero_exit_refuses_completion(self):
        fake,path,run=self.runtime_fixture(lambda runtime:runtime)
        with self.assertRaisesRegex(ValueError,'source or HEAD changed'):self.run_fixture(fake,path,run)
        self.assertEqual(json.loads((run/'targets.jsonl').read_text())['processExit'],0)

    def test_source_mutation_during_command_refuses_completion(self):
        fake,path,run=self.runtime_fixture(lambda runtime:self.root/(m.TARGET.replace('.','/')+'.lean'))
        with self.assertRaisesRegex(ValueError,'differs from HEAD'):self.run_fixture(fake,path,run)

if __name__ == '__main__':
    unittest.main()
