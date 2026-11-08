"""Guard lexical Source delivery being confused with proved original transports."""
import copy
import importlib.util
from pathlib import Path
import unittest
from unittest import mock
import tempfile
spec=importlib.util.spec_from_file_location('transport_intake_controls',Path(__file__).with_name('intake_transport_pairs.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class TransportIntakeControls(unittest.TestCase):
    def setUp(self):
        self.f={'base':m.BASE,'declarations':[]};self.p={'original_base':m.BASE,'cases':[]}
        self.packet={'pairs':[],'private_identity_gaps':[],'transport_proofs_supplied':0,'original_obligations_discharged':0}
        for kind,count in m.EXPECTED.items():
            for i in range(count):
                name=kind+str(i);private=kind=='removed-private-identity'
                old={'file':'Solidity/Fixture.lean','source_name':name,'signature_sha256':name,'variable_context':[],'visibility':'private' if private else 'public','kernel_name':'private.'+name if private else name,'elaborated':{'raw_type_sha256':name},'witness_status':'pending'}
                self.f['declarations'].append(old)
                self.p['cases'].append({'file':old['file'],'source_name':name,'kind':kind,'original_signature_sha256':name})
                row={'file':old['file'],'source_name':name,'kind':kind,'original':copy.deepcopy(old),'current':None if private else dict(old,signature_sha256='new'),
                  'current_matches_recorded_observation':True,'transport_proof':{'status':'not supplied','reference':None},'h57_authorization':'not independently verified','kernel_fidelity':'pending; no Lean executed','original_obligation_discharged':False}
                self.packet['private_identity_gaps' if private else 'pairs'].append(row)
        self.f['declarations'] += [{'file':'Solidity/Other.lean','source_name':'Other.'+str(i),'witness_status':'pending'} for i in range(770)]
    def bind(self):return m.bind(self.f,self.p,self.packet)
    def test_complete_intake_preserves_all_rows_and_no_credit(self):
        before=copy.deepcopy(self.f);out=self.bind();self.assertEqual(self.f,before);self.assertEqual(len(out['rows']),792)
        self.assertEqual([r['frozen'] for r in out['rows']],before['declarations'])
        linked=[r['transport_source_intake'] for r in out['rows'] if r['transport_source_intake'] is not None]
        self.assertEqual(len(linked),22);self.assertEqual(sum(r['private_identity_gap_retained'] for r in linked),3)
        for row in linked:
            for key in ['current_kernel_type_checked','transport_proof_supplied','h57_authorization_verified','original_credit_added','live_ownership_attested']:self.assertIs(row[key],False)
        self.assertEqual(out['original_obligations_discharged'],0);self.assertFalse(out['timing_stop_released'])
    def test_missing_duplicate_original_or_pair_refused(self):
        for target in [self.f['declarations'],self.packet['pairs']]:
            saved=copy.deepcopy(target);target.pop()
            with self.assertRaises(ValueError):self.bind()
            target[:]=saved;target[1]=copy.deepcopy(target[0])
            with self.assertRaises(ValueError):self.bind()
            target[:]=saved
    def test_original_signature_context_and_visibility_refused(self):
        row=self.packet['pairs'][0];saved=copy.deepcopy(row['original'])
        for key,value in [('signature_sha256','forged'),('variable_context',['variable (h : False)']),('visibility','private')]:
            row['original']=dict(saved,**{key:value})
            with self.assertRaises(ValueError):self.bind()
        row['original']=saved
    def test_proof_h57_kernel_promotion_refused(self):
        row=self.packet['pairs'][0];saved=copy.deepcopy(row)
        for key,value in [('transport_proof',{'status':'pass','reference':'not-a-proof'}),('h57_authorization','approved'),('kernel_fidelity','pass'),('original_obligation_discharged',True)]:
            row[key]=value
            with self.assertRaises(ValueError):self.bind()
            row.clear();row.update(copy.deepcopy(saved))
        self.packet['original_obligations_discharged']=1
        with self.assertRaises(ValueError):self.bind()
    def test_private_alias_or_partition_substitution_refused(self):
        row=self.packet['private_identity_gaps'][0];row['current']=dict(row['original'],source_name='New.public.helper')
        with self.assertRaises(ValueError):self.bind()
        row['current']=None
        self.packet['pairs'][0],self.packet['private_identity_gaps'][0]=self.packet['private_identity_gaps'][0],self.packet['pairs'][0]
        with self.assertRaises(ValueError):self.bind()
    def test_executed_buffers_are_git_bound_and_loader_restored(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);producer=root/'producer.py';helper=root/'census.py'
            first=b"import importlib.util\nfrom pathlib import Path\ns=importlib.util.spec_from_file_location('captured_helper',Path(__file__).with_name('census.py'))\nh=importlib.util.module_from_spec(s);s.loader.exec_module(h)\nvalue=h.value\n"
            buffers={str(producer):first,str(helper):b'value=7\n'}
            # Disk contents differ deliberately; execution must use retained bytes.
            producer.write_text('value=100');helper.write_text('value=200')
            factory=m.importlib.util.spec_from_file_location
            def git(command,**kwargs):return buffers[str(root/command[-1].split(':',1)[1])]
            with mock.patch.object(m,'ROOT',root),mock.patch.object(m,'PRODUCER',producer),mock.patch.object(m,'SCANNER',helper),mock.patch.object(m.subprocess,'check_output',side_effect=git):
                actual=m.execute_published(buffers,'HEAD');self.assertEqual(actual.value,7)
            self.assertIs(m.importlib.util.spec_from_file_location,factory)
            with mock.patch.object(m,'ROOT',root),mock.patch.object(m,'PRODUCER',producer),mock.patch.object(m,'SCANNER',helper),mock.patch.object(m.subprocess,'check_output',return_value=b'wrong'):
                with self.assertRaisesRegex(ValueError,'differs from Git'):m.execute_published(buffers,'HEAD')
            self.assertIs(m.importlib.util.spec_from_file_location,factory)
    def test_duplicate_json_key_refused(self):
        with self.assertRaises(ValueError):m.pairs([('x',1),('x',2)])
if __name__=='__main__':unittest.main()
