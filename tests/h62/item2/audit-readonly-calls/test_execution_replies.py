"""Guard incomplete/unbound native adapter evidence being promoted to adequacy."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('execution_reply_check',ROOT/'scripts/h62/item2/audit-readonly-calls/check_execution_replies.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

spec2=importlib.util.spec_from_file_location('execution_reply_measure',ROOT/'scripts/h62/item2/audit-readonly-calls/measure_execution_replies.py')
timing=importlib.util.module_from_spec(spec2);spec2.loader.exec_module(timing)


class ExecutionEvidenceControls(unittest.TestCase):
    def test_real_inventory_and_missing_or_extra_theorem(self):
        raw=(ROOT/m.SOURCE).read_bytes()
        self.assertEqual(len(m.theorem_inventory(raw)),11)
        for modified in [raw.replace(b'theorem fault_refused',b'theorem different_fault_refused'),
                         raw+b'\nnamespace Extra\ntheorem unaccounted : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):m.theorem_inventory(modified)

    def test_foreign_or_held_adapter_imports(self):
        raw=(ROOT/m.SOURCE).read_bytes()
        for target in [m.profile.HELD,'Foreign.Module','Solidity.Unverified']:
            with self.assertRaises(ValueError):m.theorem_inventory(b'import '+target.encode()+b'\n'+raw)

    def test_complete_axiom_records_required(self):
        rows=["'"+m.PREFIX+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in m.NAMES]
        self.assertEqual(len(m.joint.parse_axioms('\n'.join(rows),m.PREFIX,m.NAMES)),11)
        for bad in ['\n'.join(rows[:-1]),'\n'.join(rows+[rows[0]]),
                    '\n'.join(rows).replace('propext','sorryAx')]:
            with self.assertRaises(ValueError):m.joint.parse_axioms(bad,m.PREFIX,m.NAMES)

    def test_actual_timed_source_substitution_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);source=root/'ExecutionReplies.lean';log=root/'run.log'
            process=SimpleNamespace(pid=123,returncode=None)
            def changed(pid,flags):
                source.write_bytes(b'substituted')
                return pid,0,SimpleNamespace(ru_maxrss=512)
            with patch.object(timing.subprocess,'Popen',return_value=process),patch.object(timing.os,'wait4',side_effect=changed):
                with self.assertRaises(ValueError):timing.run_checked(['lean'],{},source,b'intended',log)
            with patch.object(timing.subprocess,'Popen',return_value=process),patch.object(timing.os,'wait4',return_value=(123,0,SimpleNamespace(ru_maxrss=512))):
                row=timing.run_checked(['lean'],{},source,b'intended',log)
                self.assertEqual(source.read_bytes(),b'intended');timing.seal_logs([row])
                log.write_bytes(b'substituted')
                with self.assertRaises(ValueError):timing.seal_logs([row])

    def test_transitive_held_import_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);(root/'Solidity').mkdir()
            (root/'Solidity/A.lean').write_text('import Solidity.B\n')
            (root/'Solidity/B.lean').write_text('import '+m.profile.HELD+'\n')
            with self.assertRaisesRegex(ValueError,'historically held'):
                m.profile.closure(root,['Solidity.A'],{})


if __name__=='__main__':unittest.main()
