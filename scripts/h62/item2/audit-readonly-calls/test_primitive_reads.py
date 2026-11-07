"""Guard parent-source drift and unadmitted primitive-read client inventories."""
import hashlib
import copy
import importlib.util
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock
spec=importlib.util.spec_from_file_location('primitive_reads_test_gate',Path(__file__).with_name('check_primitive_reads.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
g=m.gate
class PrimitiveReadControls(unittest.TestCase):
    def test_exact_client_inventory(self):
        raw=(g.ROOT/g.SOURCE).read_bytes()
        self.assertEqual(len(g.inventory(raw)),11)
        self.assertEqual(len(set(g.INTERFACES)),8)
        for bad in [b'import Extra.Module\n'+raw,raw+b'\nnamespace Extra\ntheorem extra : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):g.inventory(bad)
    def test_overlap_verifies_all_parent_sources(self):
        raw=b'namespace Fixture\nend Fixture\n';pin={'source_sha256':hashlib.sha256(raw).hexdigest(),'imports':[]}
        receipt={'source_pins':{'Solidity/Kept.lean':pin,'Solidity/NotLoaded.lean':pin}}
        with tempfile.TemporaryDirectory() as temp:
            parent=Path(temp)
            load=mock.Mock(return_value=receipt);read=mock.Mock(return_value=raw)
            inputs=SimpleNamespace(current=SimpleNamespace(original=SimpleNamespace(load_pinned=load)),original=SimpleNamespace(read_git=read))
            with mock.patch.object(m.OriginalCache,'__init__',return_value=None) as original:
                m.OverlapCache(inputs,parent,'frozen',{'Solidity/Kept.lean':pin},parent/'archive')
                self.assertEqual(read.call_count,2)
                self.assertEqual(set(original.call_args.args[3]),set(receipt['source_pins']))
                self.assertEqual(original.call_args.args[3]['Solidity/NotLoaded.lean'],pin)
            read.side_effect=lambda path:raw if path.endswith('Kept.lean') else b'changed'
            with self.assertRaisesRegex(ValueError,'parent source/import drift'),mock.patch.object(m.OriginalCache,'__init__',return_value=None) as original:
                m.OverlapCache(inputs,parent,'frozen',{'Solidity/Kept.lean':pin},parent/'archive')
            original.assert_not_called()
    def test_overlap_pin_substitution_refused(self):
        raw=b'namespace Fixture\nend Fixture\n';pin={'source_sha256':hashlib.sha256(raw).hexdigest(),'imports':[]}
        inputs=SimpleNamespace(current=SimpleNamespace(original=SimpleNamespace(load_pinned=lambda *args:{'source_pins':{'Solidity/A.lean':pin}})),original=SimpleNamespace(read_git=lambda _:raw))
        with self.assertRaisesRegex(ValueError,'consumer overlap source drift'),mock.patch.object(m.OriginalCache,'__init__',return_value=None):
            m.OverlapCache(inputs,Path('/not-read'),'frozen',{'Solidity/A.lean':dict(pin,source_sha256='0'*64)},Path('/not-written'))
    def test_held_dependency_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaisesRegex(ValueError,'held workload'):
                g.original.snapshot(lambda _:b'import Solidity.Backend.WorldCalls.Premises\n',g.TARGET,Path(temp))
class CoverageControls(unittest.TestCase):
    def setUp(self):
        spec=importlib.util.spec_from_file_location('read_coverage_controls',Path(__file__).with_name('primitive_read_coverage.py'))
        self.c=importlib.util.module_from_spec(spec);spec.loader.exec_module(self.c)
        rows=[{'source_name':n,'signature_sha256':n,'witness_status':'pending','elaborated':{'raw_type_sha256':n}} for n in g.INTERFACES]
        rows += [{'source_name':'Fixture.'+str(i),'signature_sha256':str(i),'witness_status':'pending'} for i in range(784)]
        self.f={'base':g.original.BASE,'declarations':rows};self.cov={'entries':[]}
        self.pair={mode:{'mode':mode,'source_sha256':'same'} for mode in ['frozen','current']}
        self.types={mode:{'declarations':[{'source_name':n,'raw_type_sha256':n} for n in g.INTERFACES]} for mode in self.pair}
        self.pins={'frozen':'f'*64,'current':'c'*64}
    def apply(self):return self.c.apply(self.f,self.cov,self.pair,self.types,self.pins)
    def test_only_selected_originals_change(self):
        before=copy.deepcopy(self.f);rows,cov,delta=self.apply()
        self.assertEqual(self.f,before);self.assertEqual(rows['declarations'][8:],before['declarations'][8:])
        self.assertEqual(delta['changed_entries'],8);self.assertEqual(len(rows['declarations']),792)
        self.assertEqual([e['proof'] for e in cov['entries']],[g.PREFIX+n for n in g.NAMES[1:9]])
    def test_missing_or_duplicate_original_identity_refused(self):
        self.f['declarations'].pop()
        with self.assertRaises(ValueError):self.apply()
        self.f['declarations'].append(copy.deepcopy(self.f['declarations'][0]))
        with self.assertRaises(ValueError):self.apply()
    def test_missing_duplicate_wrong_types_and_client_refused(self):
        original=copy.deepcopy(self.types)
        for bad in [original['current']['declarations'][:-1],original['current']['declarations']+[original['current']['declarations'][0]]]:
            self.types['current']['declarations']=bad
            with self.assertRaises(ValueError):self.apply()
        self.types=copy.deepcopy(original);self.types['current']['declarations'][0]['raw_type_sha256']='wrong'
        with self.assertRaises(ValueError):self.apply()
        self.types=original;self.pair['current']['source_sha256']='other'
        with self.assertRaises(ValueError):self.apply()
    def test_recredit_and_baseline_status_drift_refused(self):
        self.f['declarations'][0]['witness_status']='joint-witness'
        with self.assertRaises(ValueError):self.apply()
        self.cov['entries']=[{'source_name':g.INTERFACES[0],'signature_sha256':g.INTERFACES[0],'status':'pending'}]
        with self.assertRaises(ValueError):self.apply()
if __name__=='__main__':unittest.main()

