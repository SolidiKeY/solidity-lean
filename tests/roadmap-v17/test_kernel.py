"""Wire/claim rejection controls, separate from live kernel execution."""
import copy
import importlib.util
import unittest
from unittest.mock import patch
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('kernel',ROOT/'scripts/roadmap-v17-kernel.py')
k=importlib.util.module_from_spec(spec); spec.loader.exec_module(k)
class KernelControls(unittest.TestCase):
    def req(self):
        return {'schema':1,'module':'Solidity.KeySort','declarations':[{'name':'Solidity.KeySort.le_trans','kind':'theorem'}]}
    def test_request_positive(self): self.assertEqual(k.request(self.req()),self.req())
    def test_bad_requests(self):
        for key,value in [('module','Bridge.X'),('module','Solidity.X;exit'),('schema',True)]:
            r=self.req(); r[key]=value
            with self.subTest(value=value),self.assertRaises(ValueError): k.request(r)
        for name,kind in [('Lean.foo','theorem'),('Solidity.X','proof'),('Solidity.X\n','theorem')]:
            r=self.req(); r['declarations']=[{'name':name,'kind':kind}]
            with self.subTest(name=name),self.assertRaises(ValueError): k.request(r)
        r=self.req(); r['declarations']*=2
        with self.assertRaises(ValueError): k.request(r)
    def test_frame_positive(self):
        value={'schema':1,'rows':[],'imports':[],'releaseClosed':False}
        self.assertEqual(k.parse_output(k.BEGIN.encode()+b'\n'+k.canonical(value)+b'\n'+k.END.encode()+b'\n'),value)
    def test_corrupt_frames(self):
        for raw in [b'',b'V17_KERNEL_BEGIN\n{}',b'V17_KERNEL_BEGIN\n{"schema":1,"schema":1}\nV17_KERNEL_END\n',b'V17_KERNEL_BEGIN\n{}\nV17_KERNEL_END\nV17_KERNEL_END\n']:
            with self.subTest(raw=raw),self.assertRaises(ValueError): k.parse_output(raw)
    def test_closed_type(self):
        k.validate_expr(['forall',['anonymous'],'default',['sort',['zero']],['bvar','0']])
    def test_invalid_expressions(self):
        for tree in [['bvar','0'],['mvar','x'],['fvar','x'],['app',['sort',['zero']]],['sort',['mvar','u']],['const',['anonymous'],[],'extra']]:
            with self.subTest(tree=tree),self.assertRaises(ValueError): k.validate_expr(tree)
    def row(self):
        return dict(name='Solidity.KeySort.le_trans',module='Solidity.KeySort',kind='theorem',typeSha256='a'*64,valueSha256='b'*64,typeDependencies=['Bool'],valueDependencies=[],axioms=[],binderCount=5,propositionBinders=[3,4])
    def test_conditional_claim_retains_premises(self):
        r=self.row(); c={'schema':1,'declarations':[r],'semanticPremisesDischarged':False}
        result=k.match_claims(c,{'rows':[r]})
        self.assertFalse(result['semanticPremisesDischarged']); self.assertFalse(result['releaseClosed'])
    def test_forged_claims(self):
        row=self.row()
        for field,value in [('name','Solidity.KeySort.le_refl'),('module','Solidity.Other'),('kind','definition'),('typeSha256','c'*64),('valueSha256','d'*64),('axioms',['sorryAx']),('propositionBinders',[]),('binderCount',0),('typeDependencies',[]),('valueDependencies',['X'])]:
            claim=copy.deepcopy(row); claim[field]=value
            with self.subTest(field=field),self.assertRaises(ValueError): k.match_claims({'schema':1,'declarations':[claim],'semanticPremisesDischarged':False},{'rows':[row]})
        with self.assertRaises(ValueError): k.match_claims({'schema':1,'declarations':[row],'semanticPremisesDischarged':True},{'rows':[row]})
    def test_actual_axiom_output_integrity(self):
        row=self.row(); row['axioms']=['propext']
        raw=b"'Solidity.KeySort.le_trans' depends on axioms: [propext]\n"
        k.check_axiom_text(raw,[row])
        for bad in [b'',raw+raw,raw.replace(b'propext',b'sorryAx'),raw[:-3]]:
            with self.subTest(bad=bad),self.assertRaises(ValueError): k.check_axiom_text(bad,[row])
    def test_query_binds_request(self):
        r=self.req(); raw=k.query_bytes(r)
        self.assertIn(b'import Solidity.KeySort',raw); self.assertIn(b'le_trans',raw)
        other=self.req(); other['declarations'][0]['kind']='definition'
        self.assertNotEqual(raw,k.query_bytes(other))
class BindingControls(unittest.TestCase):
    def record(self):
        return dict(schema=1,exit=0,commandExit=0,before={'revision':'a'},after={'revision':'a'},installedBefore={'tool':'hash'},installedAfter={'tool':'hash'},request=KernelControls().req(),directory='/workspace/scratch/example',containerName='roadmap-v17-'+'a'*32,sourceClosure={'order':[],'modules':{}},templateSha256=k.e.digest(k.TEMPLATE.read_bytes()),querySha256=k.e.digest(k.query_bytes(KernelControls().req())),pipelineSha256='bad',attachments={})
    def test_changed_revision_tool_source_query(self):
        for field,value in [('before',{'revision':'other'}),('after',{'revision':'other'}),('installedAfter',{}),('installedBefore',{}),('sourceClosure',{}),('querySha256','bad'),('templateSha256','bad'),('commandExit',1),('exit',1)]:
            r=self.record(); r[field]=value
            with self.subTest(field=field),patch.object(k,'tool_inputs',return_value={'tool':'hash'}),patch.object(k,'source_closure',return_value={'order':[],'modules':{}}),self.assertRaises(ValueError):
                k.validate_record(r,{'revision':'a'})
    def test_runtime_rejects_missing_and_unknown_measurements(self):
        r=dict(headroomBytes=2*1024**3,diskFreeBytes=1024**3,freshStartAbsent=True,sampleFormat=k.p.SAMPLE_FORMAT,elapsedSeconds=1,sourceClosure={'order':[]},attachments={})
        with self.assertRaises(ValueError): k.check_runtime(r,{},Path('/workspace/scratch/example'))
        r['headroomBytes']=0
        with self.assertRaises(ValueError): k.check_runtime(r,{},Path('/workspace/scratch/example'))
if __name__=='__main__': unittest.main()
