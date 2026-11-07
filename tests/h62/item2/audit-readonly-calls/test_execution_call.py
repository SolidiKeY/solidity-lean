"""Guard stale-parent, split-read log and partial caller-frame evidence."""
import importlib.util
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('execution_call_check',ROOT/'scripts/h62/item2/audit-readonly-calls/check_execution_call.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class CallerEvidenceControls(unittest.TestCase):
    def test_parent_authenticated_before_parse(self):
        class Forged:
            def read_bytes(self):return b'not-json'
        with self.assertRaisesRegex(ValueError,'unadmitted'):m.read_parent(Forged())

    def test_complete_module_inventories(self):
        for source,checked,count in [(m.SOURCE,False,11),(m.CHECKED_SOURCE,True,6)]:
            raw=(ROOT/source).read_bytes();self.assertEqual(len(m.inventory(raw,checked)),count)
            for bad in [b'import Foreign.Module\n'+raw,raw+b'\nnamespace Extra\ntheorem unaccounted : True := True.intro\nend Extra\n']:
                with self.subTest(source=source),self.assertRaises(ValueError):m.inventory(bad,checked)

    def test_axiom_refusals(self):
        for prefix,names in [(m.PREFIX,m.NAMES),(m.CHECKED_PREFIX,m.CHECKED_NAMES)]:
            rows=["'"+prefix+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names]
            self.assertEqual(len(m.m.joint.parse_axioms('\n'.join(rows),prefix,names)),len(names))
            for bad in ['\n'.join(rows[:-1]),'\n'.join(rows+[rows[0]]),'\n'.join(rows).replace('propext','sorryAx')]:
                with self.assertRaises(ValueError):m.m.joint.parse_axioms(bad,prefix,names)

    def test_one_log_buffer_and_final_mutation_refusal(self):
        class ChangingLog:
            reads=0
            def read_bytes(self):
                self.reads+=1
                return b'actual Lean output' if self.reads==1 else b'forged axiom output'
            def read_text(self):raise AssertionError('separate text read must not be used')
        changing=ChangingLog();digest,text=m.captured_log(changing)
        self.assertEqual(changing.reads,1);self.assertEqual(text,'actual Lean output')
        self.assertEqual(digest,hashlib.sha256(text.encode()).hexdigest())
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'proof.log';path.write_text(text);m.m.check.verify_hashes({str(path):digest})
            path.write_text('forged axiom output')
            with self.assertRaises(ValueError):m.m.check.verify_hashes({str(path):digest})

    def test_parent_flat_project_objects_and_log_mutation(self):
        with tempfile.TemporaryDirectory() as temp:
            parent=Path(temp);native=parent/'library/ExecutionReplies.olean';native.parent.mkdir();native.write_bytes(b'native')
            project=parent/'library/Solidity/A.olean';project.parent.mkdir();project.write_bytes(b'project')
            log=parent/'compile.log';log.write_bytes(b'passed')
            pins={'Solidity/A.lean':{'source_sha256':'synthetic-source','imports':[]}}
            receipt={'project_order':[],'source_pins':pins,'protected_sha256':{str(log):m.m.check.sha(log)},
                     'steps':[{'log':str(log),'sha256':m.m.check.sha(log)}],
                     'artifacts':{m.m.SOURCE:{'source_sha256':m.m.check.sha(ROOT/m.m.SOURCE),'artifact_sha256':m.m.check.sha(native)},
                                  'Solidity/A.lean':{'artifact_sha256':m.m.check.sha(project)}}}
            with patch.object(m.m.profile,'closure',return_value=([],pins)):
                m.verify_parent(parent,receipt)
                for path in [native,project,log]:
                    saved=path.read_bytes();path.write_bytes(b'substituted')
                    with self.subTest(path=path),self.assertRaises(ValueError):m.verify_parent(parent,receipt)
                    path.write_bytes(saved)
                project.unlink()
                with self.assertRaises(OSError):m.verify_parent(parent,receipt)

    def test_canonical_project_and_flat_roots(self):
        root=Path('/owned/output')
        project=root/'staged/Solidity/Backend/InternalFlow/RuntimeFrameP1V2CallAgreement.lean'
        own=root/'ExecutionCall.lean'
        self.assertEqual(m.module_root(root,project),root/'staged')
        self.assertEqual(m.module_root(root,own),root)
        self.assertEqual(project.relative_to(m.module_root(root,project)).with_suffix('').as_posix().replace('/','.'),
                         'Solidity.Backend.InternalFlow.RuntimeFrameP1V2CallAgreement')
        pairs,text=m.identity_probe();self.assertEqual(len(pairs),5)
        self.assertIn('getModuleIdxFor?',text);self.assertNotIn('staged.Solidity',text)

    def test_held_dependency_refused(self):
        with patch.object(m.m.profile,'closure',return_value=([m.HELD],{})):
            with self.assertRaisesRegex(ValueError,'held Premises'):m.checked_closure()
        with patch.object(m.m.profile,'closure',return_value=(['unheld'],{'pin':'value'})):
            self.assertEqual(m.checked_closure(),(['unheld'],{'pin':'value'}))

    def test_parent_graph_drift_refused(self):
        with patch.object(m.m.profile,'closure',return_value=(['different'],{})):
            with self.assertRaisesRegex(ValueError,'source/import drift'):
                m.verify_parent(Path('/unused'),{'project_order':[],'source_pins':{}})


if __name__=='__main__':unittest.main()
