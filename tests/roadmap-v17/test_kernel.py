"""Wire/claim rejection controls, separate from live kernel execution."""
import copy
import importlib.util
import unittest
import tempfile
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
        req=KernelControls().req(); out=Path('/workspace/scratch/example'); closure={'order':[],'modules':{}}
        return dict(schema=1,exit=0,commandExit=0,before={'revision':'a'},after={'revision':'a'},installedBefore={'tool':'hash'},installedAfter={'tool':'hash'},request=req,directory=str(out),containerName='roadmap-v17-'+'a'*32,sourceClosure=closure,templateSha256=k.e.digest(k.TEMPLATE.read_bytes()),querySha256=k.e.digest(k.query_bytes(req)),pipelineSha256=k.e.digest(k.pipeline_bytes(req,closure,out)),attachments={},result={'rows':[]},semanticPremisesDischarged=False,releaseClosed=False)
    def validate(self,r):
        argv=['canonical']; current={'revision':'a'}
        original_read=Path.read_bytes
        def read(path):
            return k.canonical(argv) if str(path).startswith('/workspace/scratch/example/') else original_read(path)
        with patch.object(k,'tool_inputs',return_value={'tool':'hash'}),patch.object(k,'source_closure',return_value={'order':[],'modules':{}}),patch.object(k.p,'docker_create_argv',return_value=argv),patch.object(k,'check_runtime'),patch.object(k,'parse_output',return_value={}),patch.object(k,'normalize_output',return_value={'rows':[]}),patch.object(k,'check_axiom_text'),patch.object(Path,'read_bytes',read):
            # Supply the runtime path used to normalize toolchain aliases.
            current['runtime']={'lean':{'path':'/installed/bin/lean'}}
            r=copy.deepcopy(r)
            r['before'].update(runtime=current['runtime']); r['after'].update(runtime=current['runtime'])
            return k.validate_record(r,current)
    def test_baseline_and_changed_bindings(self):
        self.assertEqual(self.validate(self.record()),KernelControls().req())
        for field,value,reason in [('before',{'revision':'other'},'stale source'),('after',{'revision':'other'},'stale source'),('installedAfter',{},'installed import'),('installedBefore',{},'installed import'),('sourceClosure',{},'source import closure'),('querySha256','bad','query/template'),('templateSha256','bad','query/template'),('pipelineSha256','bad','pipeline'),('commandExit',1,'command exit'),('exit',1,'extraction gate')]:
            r=self.record(); r[field]=value
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,reason): self.validate(r)
    def test_missing_runtime_and_headroom(self):
        r=dict(headroomBytes=2*1024**3,diskFreeBytes=1024**3,freshStartAbsent=True,sampleFormat=k.p.SAMPLE_FORMAT,elapsedSeconds=1,sourceClosure={'order':[]},attachments={})
        with self.assertRaisesRegex(ValueError,'mandatory extraction attachment'): k.check_runtime(r,{},Path('/workspace/scratch/example'))
        r['headroomBytes']=0
        with self.assertRaisesRegex(ValueError,'headroom/disk'): k.check_runtime(r,{},Path('/workspace/scratch/example'))
class RuntimeControls(unittest.TestCase):
    def test_valid_runtime_then_corruptions(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp); req=KernelControls().req(); closure={'order':[],'modules':{}}
            current={'runtime':{'lean':{'path':'/tools/bin/lean','version':'lean version','sha256':'a'*64},'lake':{'path':'/tools/bin/lake','version':'lake version','sha256':'b'*64}},'buildTools':{tool:{'sha256':'c'*64} for tool in k.e.BUILD_TOOL_NAMES}}
            r=dict(request=req,sourceClosure=closure,headroomBytes=2*1024**3,diskFreeBytes=1024**3,freshStartAbsent=True,sampleFormat=k.p.SAMPLE_FORMAT,elapsedSeconds=1,samples=[{'leanWorkers':1,'unclassifiedLeanWorkers':0,'unknownLeanProcesses':[]}],attachments={})
            files={'request.json':k.canonical(req),'Query.lean':k.query_bytes(req),'Axioms.lean':k.axiom_query(req),'pipeline.sh':k.pipeline_bytes(req,closure,out),'execution.sh':k.p.execution_script(out,['sh',str(out/'pipeline.sh')],Path('/tools/bin/lake')).encode(),'docker-argv.json':b'[]','command.stdout':b'','query.stdout':b'','query.stderr':b'','axioms.stdout':b'','axioms.stderr':b'','memoryMax':str(k.p.CAP).encode(),'swapMax':b'0','memoryPeak':b'123','realLeanSha256':b'a'*64,'lakeSha256':b'b'*64,'leanVersion':b'lean version','lakeVersion':b'lake version','leanNumThreads':b'1'}
            for tool in k.e.BUILD_TOOL_NAMES:
                files[tool+'-launcher']=k.p.launcher_bytes(tool); files['tool-'+tool]=b'c'*64; files['entrypoint-'+tool]=k.e.digest(k.p.launcher_bytes(tool)).encode()
            for name,data in files.items(): (out/name).write_bytes(data)
            r['attachments']={name:k.e.digest(data) for name,data in files.items()}
            k.check_runtime(r,current,out)
            for key,value,reason in [('samples',[{'leanWorkers':2,'unclassifiedLeanWorkers':0,'unknownLeanProcesses':[]}],'process samples'),('samples',[{'leanWorkers':0,'unclassifiedLeanWorkers':1,'unknownLeanProcesses':['unknown']}],'process samples'),('attachments',{},'mandatory'),('freshStartAbsent',False,'fresh execution'),('elapsedSeconds',3010,'budget')]:
                bad=copy.deepcopy(r); bad[key]=value
                with self.subTest(key=key,value=value),self.assertRaisesRegex(ValueError,reason): k.check_runtime(bad,current,out)
            for name,data in [('swapMax',b'1'),('memoryMax',b'999'),('Query.lean',b'forged'),('tool-lean',b'bad')]:
                old=(out/name).read_bytes(); (out/name).write_bytes(data)
                with self.subTest(file=name),self.assertRaises(ValueError): k.check_runtime(r,current,out)
                (out/name).write_bytes(old)

class OutputControls(unittest.TestCase):
    def payload(self):
        req=KernelControls().req(); n=req['declarations'][0]['name']
        row=dict(name=n,nameAst=k.name_ast(n),module=req['module'],kind='theorem',unsafe=False,partial=False,levels=[],type=['sort',['zero']],value=['sort',['zero']],typeDisplaySupplemental='supplemental',typeDependencies=[],valueDependencies=[],axioms=[],binderCount=0,propositionBinders=[],semanticPremisesDischarged=False)
        return req,{'schema':1,'rows':[row],'imports':[],'releaseClosed':False}
    def test_identity_and_stale_import_rejections(self):
        req,payload=self.payload(); out=Path('/workspace/scratch/example'); closure={'modules':{}}
        result=k.normalize_output(copy.deepcopy(payload),req,out,closure,{},Path('/tools'))
        self.assertFalse(result['semanticPremisesDischarged'])
        for key,value in [('name','Solidity.KeySort.other'),('module','Solidity.Other'),('kind','definition'),('nameAst',k.name_ast('Other')),('typeDependencies',['forged']),('value',None),('semanticPremisesDischarged',True)]:
            bad=copy.deepcopy(payload); bad['rows'][0][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError): k.normalize_output(bad,req,out,closure,{},Path('/tools'))
        payload['imports']=[{'module':'Solidity.KeySort','olean':'/stale/Solidity/KeySort.olean'}]
        with self.assertRaisesRegex(ValueError,'stale/unexpected'): k.normalize_output(payload,req,out,closure,{},Path('/tools'))
class ReplayControls(unittest.TestCase):
    def test_exact_replay_binding(self):
        old=dict(before={'revision':'a'},after={'revision':'a'},installedBefore={'tool':'hash'},installedAfter={'tool':'hash'},result={'rows':[]})
        k.match_replay(old,copy.deepcopy(old))
        for key,value in [('before',{'revision':'other'}),('after',{'revision':'other'}),('installedBefore',{}),('installedAfter',{}),('result',{'rows':['forged']})]:
            replay=copy.deepcopy(old); replay[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError): k.match_replay(old,replay)
if __name__=='__main__': unittest.main()
