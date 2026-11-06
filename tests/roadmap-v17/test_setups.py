import copy,importlib.util,json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2]
def load(name):
 spec=importlib.util.spec_from_file_location(name,ROOT/('scripts/roadmap-v17-'+name+'.py'));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
p=load('provenance');s=load('setups');t=load('timing')
class SetupControls(unittest.TestCase):
 def test_exact_published24_and_command_contract(self):
  self.assertEqual(p.setup_modules(),t.MODULES);self.assertEqual(len(p.setup_modules()),24)
  for i,module in enumerate(t.MODULES):
   command=p.gate_command(f'derived17-setup-{i:02}',Path('/tmp/new-stage'))
   self.assertEqual(command[1:4],['-I','-S','-B']);self.assertIn('capture',command);self.assertEqual(command[command.index('--module')+1],module)
 def test_missing_partial_wrong_revision_or_order_preparation(self):
  current={'revision':'real'}
  for value in [{},{'kind':'actual-Lake-original24-setups','sourceSnapshot':{'revision':'wrong'}},{'kind':'actual-Lake-original24-setups','sourceSnapshot':current,'expectedModules':t.MODULES,'stages':[]}]:
   with self.assertRaises((ValueError,KeyError)):s.validate(value,Path('/tmp'),current)
 def test_actual_setup_capture_artifact_mutations(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);out=root/'evidence';out.mkdir();module=t.MODULES[0];source=root/(module.replace('.','/')+'.lean');source.parent.mkdir(parents=True);source.write_text('synthetic bookkeeping input only')
   target=root/'.lake/build/ir'/(module.replace('.','/')+'.setup.json');target.parent.mkdir(parents=True);artifact=root/'.lake/build/lib/lean/Input.olean';artifact.parent.mkdir(parents=True);artifact.write_bytes(b'original')
   value={'name':module,'isModule':False,'importArts':{'Input':[str(artifact)]},'plugins':[],'dynlibs':[]};raw=json.dumps(value).encode();target.write_bytes(raw);(out/'lake-setup.stdout').write_bytes(raw);(out/'lake-setup.stderr').write_bytes(b'')
   current={'sourceToolchainKey':'key','runtime':{'lean':{'path':str(root/'tool/bin/lean')}}}
   with patch.object(p,'ROOT',root):
    actual=p.setup_output(out,current,'derived17-setup-00');self.assertEqual(actual['module'],module);self.assertEqual(actual['importArtifacts'][str(artifact)],p.resources.hash_file(artifact))
    record={'setupOutput':actual,'buildEnd':{'files':{'ir/'+module.replace('.','/')+'.setup.json':p.e.digest(raw)}}}
    self.assertTrue(p.validate_setup_output(record,out,current,'derived17-setup-00'))
    for key,badvalue in [('importArtifacts',{}),('generatedSha256','f'*64),('generatedSetup',str(root/'wrong'))]:
     bad=copy.deepcopy(record);bad['setupOutput'][key]=badvalue
     with self.subTest(key=key),self.assertRaises(ValueError):p.validate_setup_output(bad,out,current,'derived17-setup-00')
    artifact.write_bytes(b'changed')
    with self.assertRaises(ValueError):p.validate_setup_output(record,out,current,'derived17-setup-00')
    artifact.write_bytes(b'original')
    target.write_bytes(b'forged')
    with self.assertRaises(ValueError):p.setup_output(out,current,'derived17-setup-00')
    target.write_bytes(raw);value['name']='wrong';(out/'lake-setup.stdout').write_text(json.dumps(value))
    with self.assertRaises(ValueError):p.setup_output(out,current,'derived17-setup-00')
 def test_selected_lake_bin_in_capture_child_path(self):
  import inspect
  source=inspect.getsource(s.capture)
  self.assertIn("env['PATH']=str(lake.parent)",source);self.assertIn('lake.parent==lean.parent',source)

 def test_complete24_accounting_and_mutations(self):
  # Synthetic accounting only; p.validate authentication is tested separately.
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);current={'revision':'same'};records={};stages=[];setups={};files={}
   for i,module in enumerate(t.MODULES):
    d=root/str(i);d.mkdir();raw=json.dumps({'name':module}).encode();(d/'stdout').write_bytes(raw)
    generated=root/(str(i)+'.setup');generated.write_bytes(raw);files['ir/'+module.replace('.','/')+'.setup.json']=p.e.digest(raw)
    obs={'stdout':{'path':'stdout','sha256':p.e.digest(raw)},'generatedSetup':str(generated),'generatedSha256':p.e.digest(raw),'importArtifacts':{}}
    record={'setupOutput':obs,'buildStart':{'files':dict(files)},'buildEnd':{'files':dict(files)},'cacheStart':{},'cacheEnd':{},'installedAfter':{}}
    if i:record['buildStart']=copy.deepcopy(records[str(root/str(i-1)/'record')]['buildEnd'])
    rp=d/'record';rp.write_text(json.dumps(record));records[str(rp)]=record
    stages.append({'module':module,'path':str(rp.relative_to(root)),'sha256':p.resources.hash_file(rp)})
    setups[module]={'path':str(generated),'sha256':p.e.digest(raw)}
   good={'kind':'actual-Lake-original24-setups','sourceSnapshot':current,'sourceAfter':current,'freshProofWorkloadPass':False,'releaseClosed':False,'expectedModules':t.MODULES,'stages':stages,'setups':setups,'installedInputs':{},'finalBuild':copy.deepcopy(record['buildEnd']),'finalCache':{}}
   with patch.object(s,'protocol',return_value=p),patch.object(p,'validate',return_value=True):
    self.assertTrue(s.validate(good,root,current,False))
    mutations=[('sourceAfter',{}),('releaseClosed',True),('freshProofWorkloadPass',True),('failure',{'exit':124}),('finalCache',{'forged':'cache'}),('finalBuild',{'files':{'unrecorded':'hash'}}),('stages',stages[::-1]),('setups',dict(setups,forged={'path':'wrong','sha256':'f'*64}))]
    for key,value in mutations:
     bad=copy.deepcopy(good);bad[key]=value
     with self.subTest(key=key),self.assertRaises((ValueError,KeyError)):s.validate(bad,root,current,False)
