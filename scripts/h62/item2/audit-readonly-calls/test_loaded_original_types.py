"""Guard missing/private/unloaded metadata rows and false witness credit."""
import copy
import importlib.util
from pathlib import Path
import unittest
spec=importlib.util.spec_from_file_location('loaded_types_controls',Path(__file__).with_name('loaded_original_types.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class LoadedTypeControls(unittest.TestCase):
    def setUp(self):
        self.selected=[];self.obs=[];self.types=[];self.lexical=[];lines=[]
        for i in range(49):
            name='t'+str(i);source='N.'+name;expr='Type '+source;module='Solidity.Fixture'
            old={'source_name':source,'kernel_name':source,'file':'Solidity/Fixture.lean','visibility':'public','signature_sha256':name,'variable_context':[],'witness_status':'pending','elaborated':{'raw_type_sha256':m.sha(expr.encode())}}
            self.selected.append(old);lines.append(name)
            self.obs.append({'source_name':source,'kernel_name':source,'expected_module':module,'actual_module':module,'status':'present','selection':{'start':{'line':i+1,'column':0},'end':{'line':i+1,'column':len(name)}}})
            self.types.append({'source_name':source,'kernel_name':source,'module':module,'raw_type_expr':expr,'pretty_type':expr})
            start=sum(len(x)+1 for x in lines[:-1]);self.lexical.append({'source_name':source,'signature_sha256':name,'variable_context':[],'visibility':'public','name_token':name,'name_byte_range':{'start':start,'end':start+len(name)}})
        self.frozen={'declarations':copy.deepcopy(self.selected)+[{'source_name':'Other.'+str(i),'file':'Solidity/Other.lean','witness_status':'pending'} for i in range(743)]}
        self.raw='\n'.join(lines).encode()
        def position(raw,pos):
            lines=raw.decode().split('\n');return len(('\n'.join(lines[:pos['line']-1])+('\n' if pos['line']>1 else '')+lines[pos['line']-1][:pos['column']]).encode())
        self.position=position
    def run_join(self):return m.join(self.frozen,self.selected,self.obs,self.types,{'Solidity/Fixture.lean':self.raw},{'Solidity/Fixture.lean':self.lexical},self.position)
    def test_all792_and_no_credit(self):
        before=copy.deepcopy(self.frozen);result=self.run_join();self.assertEqual(self.frozen,before)
        self.assertEqual(len(result['rows']),792);self.assertEqual(result['matched_types'],49)
        self.assertEqual(result['kernel_statuses']['not-loaded-by-admitted-closure'],743)
        self.assertEqual([r['frozen'] for r in result['rows']],before['declarations'])
        self.assertTrue(all(not r['original_credit_added'] and not r['live_ownership_verified'] for r in result['rows']))
    def test_missing_private_identity_is_not_aliased(self):
        self.selected[0]['kernel_name']='_private.Solidity.Fixture.0.N.t0';self.frozen['declarations'][0]['kernel_name']=self.selected[0]['kernel_name'];self.obs[0].update(kernel_name=self.selected[0]['kernel_name'],status='missing-original-kernel',selection=None);self.types.pop(0)
        result=self.run_join();self.assertEqual(result['rows'][0]['current_kernel_status'],'missing-original-kernel')
        self.assertNotIn('current_type',result['rows'][0])
    def test_missing_duplicate_or_wrong_identity_refused(self):
        saved=copy.deepcopy(self.obs)
        for bad in [saved[:-1],saved+[saved[0]]]:
            self.obs=bad
            with self.assertRaises(ValueError):self.run_join()
        self.obs=saved;self.types[0]['kernel_name']='replacement'
        with self.assertRaises(ValueError):self.run_join()
    def test_range_mismatch_refused_and_missing_range_retained(self):
        saved=copy.deepcopy(self.obs[0]['selection']);self.obs[0]['selection']['end']['column']=1
        with self.assertRaises(ValueError):self.run_join()
        self.obs[0]['selection']=None;result=self.run_join();self.assertEqual(result['rows'][0]['source_binding'],'missing-direct-range')
    def test_same_token_other_location_refused(self):
        self.raw+=b'\nt0';self.obs[0]['selection']={'start':{'line':50,'column':0},'end':{'line':50,'column':2}}
        with self.assertRaises(ValueError):self.run_join()
    def test_changed_type_keeps_original_pending(self):
        self.types[0]['raw_type_expr']='changed';result=self.run_join()
        self.assertEqual(result['changed_types'],1);self.assertEqual(result['rows'][0]['frozen']['witness_status'],'pending');self.assertFalse(result['runtime_gate_pass'])
if __name__=='__main__':unittest.main()
