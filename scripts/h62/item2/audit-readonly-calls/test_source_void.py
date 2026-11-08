"""Guard helper substitution, omitted Source/native closure and added proof cases."""
import importlib.util
from pathlib import Path
import tempfile
import types
import unittest
from unittest.mock import patch
spec=importlib.util.spec_from_file_location('source_void_controls',Path(__file__).with_name('check_source_void.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class SourceVoidControls(unittest.TestCase):
    def test_exact_inventory(self):
        raw=(m.ROOT/m.SOURCE).read_bytes()
        self.assertEqual(len(m.inventory(raw)),17)
        for bad in [b'import Lean\n'+raw,raw.replace(b'theorem source_call',b'theorem renamed_call'),raw+b'\nnamespace Extra\ntheorem padding : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):m.inventory(bad)
    def test_complete_closure_and_hold(self):
        with patch.object(m.m.profile,'closure',return_value=([],{})) as closure:
            self.assertEqual(m.closure(),([],{}))
            self.assertEqual(closure.call_args.args[1],[m.m.TARGET,m.frame.legacy.CHECKED_TARGET,'Solidity.Source.SemanticsExamples'])
        with patch.object(m.m.profile,'closure',return_value=([m.frame.legacy.HELD],{})):
            with self.assertRaises(ValueError):m.closure()
    def _helper_substitution(self,saved):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'project';scripts=root/'scripts';scripts.mkdir(parents=True)
            entry=scripts/'entry.py';a=scripts/'a.py';b=scripts/'b.py'
            for file in [entry,a,b]:file.write_text('unchanged helper data')
            first=types.ModuleType('first');second=types.ModuleType('second')
            first.__file__=str(a);second.__file__=str(b);first.peer=second;second.peer=first
            foreign=types.ModuleType('foreign');foreign.__file__=str(Path(tmp)/'outside.py');first.external=foreign
            with patch.object(m,'ROOT',root),patch.object(m,'__file__',str(entry)):
                pins,snapshots=m.capture_tools([first],Path(tmp)/'evidence',require_loaded=False)
            self.assertEqual(set(snapshots),{str(entry),str(a),str(b)})
            m.m.check.verify_hashes(pins)
            target=Path(snapshots[str(b)]['saved']) if saved else b
            target.write_text('substituted bytes')
            with self.assertRaises(ValueError):m.m.check.verify_hashes(pins)
    def test_actual_helper_executes_retained_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'project';scripts=root/'scripts';scripts.mkdir(parents=True)
            file=scripts/'helper.py';file.write_bytes(b'value = 7\n')
            loader=importlib.machinery.SourceFileLoader('retained_helper',str(file))
            with patch.object(m,'ROOT',root):code=m.retained_get_code(loader,'retained_helper')
            file.write_bytes(b'value = 9\n');namespace={};exec(code,namespace)
            self.assertEqual(namespace['value'],7)
            self.assertEqual(m.LOADED_HELPER_BYTES[file.resolve()],b'value = 7\n')
            with patch.object(m,'ROOT',root):
                with self.assertRaises(ValueError):m.retained_get_code(loader,'retained_helper')
    def test_unretained_helper_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'project';scripts=root/'scripts';scripts.mkdir(parents=True)
            entry=scripts/'entry.py';file=scripts/'helper.py'
            entry.write_text('entry = True');file.write_text('value = 7')
            helper=types.ModuleType('helper');helper.__file__=str(file)
            with patch.object(m,'ROOT',root),patch.object(m,'__file__',str(entry)):
                with self.assertRaises(ValueError):m.capture_tools([helper],Path(tmp)/'evidence')
    def test_transitive_loaded_helper_substitution_refused(self):self._helper_substitution(False)
    def test_saved_helper_substitution_refused(self):self._helper_substitution(True)
if __name__=='__main__':unittest.main()
