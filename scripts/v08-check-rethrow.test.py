#!/usr/bin/env python3
"""Adversarial evidence checks; never edits Lean sources or deletes fixtures.
These are external validation tests, separate from kernel negative controls.
"""
import copy, json, subprocess, sys, tempfile
from pathlib import Path
root = Path(__file__).resolve().parent.parent
original = json.loads(Path(sys.argv[1]).read_text())
# Never overwrite prior checkpoint fixtures or remove this persistent directory.
fixtures = Path(tempfile.mkdtemp(prefix='v08-evidence-controls-', dir='/workspace/v08-world-lowering-evidence'))
checker = root/'scripts/v08-check-rethrow.py'
def check(name, result, expected):
 path=fixtures/(name+'.json');path.write_text(json.dumps(result,indent=2)+'\n')
 proc=subprocess.run([sys.executable,str(checker),str(path)],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (fixtures/(name+'.log')).write_text('exit='+str(proc.returncode)+'\n'+proc.stdout)
 assert (proc.returncode==0)==expected, (name,proc.stdout)
check('valid-current-evidence',copy.deepcopy(original),True)
for name,key,value in [('guard-stop','guard_stop','corrupted-guard'),('zero-samples','samples',0),('changed-during-build','source_unchanged',False),('changed-log','log_sha256','0'*64)]:
 result=copy.deepcopy(original);result[key]=value;check(name,result,False)
result=copy.deepcopy(original);key=next(iter(result['source_sha256']));result['source_sha256'][key]='0'*64;check('changed-source',result,False)
result=copy.deepcopy(original);result['source_sha256'].pop(next(iter(result['source_sha256'])));check('missing-source',result,False)
result=copy.deepcopy(original);result['config_sha256']='0'*64;check('changed-config',result,False)
result=copy.deepcopy(original);result['tool_versions'][0]='wrong toolchain';check('wrong-toolchain',result,False)
result=copy.deepcopy(original);result['cleanup_verified']=False;check('unconfirmed-container-stop',result,False)
handler='Solidity/Lowering/V08/HandlerControls.lean'
assert handler in original['source_sha256'], 'handler source absent from current evidence'
result=copy.deepcopy(original);result['source_sha256'][handler]='0'*64;check('changed-handler-source',result,False)
result=copy.deepcopy(original);result['source_sha256'].pop(handler);check('missing-handler-source',result,False)
library_handler='Solidity/Lowering/V08/LibraryHandlerControls.lean'
assert library_handler in original['source_sha256'], 'library-handler source absent from current evidence'
result=copy.deepcopy(original);result['source_sha256'][library_handler]='0'*64;check('changed-library-handler-source',result,False)
result=copy.deepcopy(original);result['source_sha256'].pop(library_handler);check('missing-library-handler-source',result,False)
print('PASS: current evidence accepted; thirteen corrupted/guarded evidence controls rejected; fixtures='+str(fixtures))

success='Solidity/Lowering/V08/CreationSuccessControls.lean'
assert success in original['source_sha256']
result=copy.deepcopy(original);result['source_sha256'][success]='0'*64;check('changed-success-creation-source',result,False)
result=copy.deepcopy(original);result['source_sha256'].pop(success);check('missing-success-creation-source',result,False)
print('PASS: fifteen corruption controls rejected after accepting current positive evidence')

for module in ['TransactionPrefixes','PrefixControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: nineteen corruption controls rejected after positive current evidence')

for module in ['SourceKeccak','SourceKeccakControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: actual Source Keccak evidence corruption controls rejected')

for module in ['SourceEmit','SourceEmitControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: source emit evidence corruption controls rejected')

for module in ['SourceCallable','SourceCallableControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: source callable evidence corruption controls rejected')

for module in ['SourceDispatch','SourceDispatchControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: source dispatch evidence corruption controls rejected')

for module in ['SourceCustomErrors','SourceCustomErrorControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: source custom-error evidence corruption controls rejected')

# Additive coverage: every earlier case remains verbatim above.
for module in ['SourceCustomErrorFailures','SourceCustomErrorFailureControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: source custom-error failure evidence corruption controls rejected')

# Additive ABI-expression evidence controls; all earlier44 cases remain verbatim.
for module in ['SourceAbi','SourceAbiControls']:
 path='Solidity/Lowering/V08/'+module+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+module,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+module,result,False)
print('PASS: source ABI expression evidence corruption controls rejected')

# Additive source-transient leaf binding; all48 earlier cases remain verbatim.
path='Solidity/Lowering/V08/SourceTransient.lean'
assert path in original['source_sha256']
result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-SourceTransient',result,False)
result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-SourceTransient',result,False)
print('PASS: actual source transient evidence corruption controls rejected')

# Same fifty historical corruption meanings, using the new native schema.
for name,key,value in [('wrong-exit','actual_container_exit',1),('wrong-runtime','container_id','0'*64),('wrong-cumulative','cumulative_raw_log_sha256','0'*64),('wrong-prefix','log_prefix_sha256','0'*64),('old-containers-drift','old_containers_unchanged',False),('invalid-measurement','measurement_and_bindings_valid',False),('monitor-error','monitor_error',{'type':'corrupt'}),('wrong-base','candidate_base','0'*40),('wrong-peak','cgroup_peak',0),('wrong-RSS','peak_aggregate_rss',0)]:
 result=copy.deepcopy(original);result[key]=value;check(name,result,False)
path='Solidity/Lowering/V08/SourceAbiEntryControls.lean'
for name,missing in [('changed-SourceAbiEntryControls',False),('missing-SourceAbiEntryControls',True)]:
 result=copy.deepcopy(original)
 if missing:result['source_sha256'].pop(path)
 else:result['source_sha256'][path]='0'*64
 check(name,result,False)
print('PASS: all50starting cases (onepositive/49negative) plus12current-native-schema corruptions rejected after actual positive')

# Exact profile/image/environment checks on actual descriptors, then corruption.
import importlib.util
spec=importlib.util.spec_from_file_location('native099',checker)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
operation=json.loads((Path(original['log']).parent/'operation-started.json').read_bytes())
profile=operation['profile'];module.validate_profile(profile)
for name,key,value in [('memory','Memory',1),('swap','MemorySwap',0),('cpu','NanoCpus',2_000_000_000),('network','NetworkMode','host')]:
 bad=copy.deepcopy(profile);bad['HostConfig'][key]=value
 try:module.validate_profile(bad)
 except AssertionError:pass
 else:raise AssertionError('accepted profile '+name)
observed=module.docker_get('/containers/'+module.CID+'/json')
image=module.docker_get('/images/'+profile['Image']+'/json')
module.validate_image_environment(observed,profile,image,image['Id'])
for name in ['extra-env','wrong-image']:
 bad=copy.deepcopy(observed)
 if name=='extra-env':bad['Config']['Env'].append('UNEXPECTED_NONSECRET=1')
 else:bad['Image']='sha256:'+'0'*64
 try:module.validate_image_environment(bad,profile,image,image['Id'])
 except AssertionError:pass
 else:raise AssertionError('accepted '+name)
for name,key,value in [('wrong-name','name','other'),('wrong-token','token','other')]:
 result=copy.deepcopy(original);result[key]=value;check(name,result,False)
print('PASS:4 exact-profile and2 complete-image/environment corruption controls;2 name/token record controls')

# Additive actual-rethrow binding controls; all70 earlier cases retained.
for leaf in ['SourceRethrow','SourceRethrowControls']:
 path='Solidity/Lowering/V08/'+leaf+'.lean'
 assert path in original['source_sha256']
 result=copy.deepcopy(original);result['source_sha256'][path]='0'*64;check('changed-'+leaf,result,False)
 result=copy.deepcopy(original);result['source_sha256'].pop(path);check('missing-'+leaf,result,False)
pins=(root/'scripts/v08-axiom-pins.json').read_bytes()
native=(root/'scripts/v08-check-public099.py').read_bytes()
assert len(module.validate_base_inputs(pins,native))==858
for name,p,c in [('changed-prior-pins',pins+b' ',native),('changed-native-checker',pins,native+b'#corrupt'),('missing-prior-pin',b'{}',native)]:
 try:module.validate_base_inputs(p,c)
 except AssertionError:pass
 else:raise AssertionError('accepted '+name)
print('PASS:77 total case intents (one original evidence positive and76 negatives), plus real descriptor/base positives; prior70 cases unchanged')

# Extra proof inventory validation uses the same production helper, with no
# mutation of actual files/seals and no trust-baseline rewrite.
extra=json.loads((root/'scripts/v08-rethrow-axiom-pins.json').read_bytes())
prior=module.validate_base_inputs(pins,native)
assert len(module.validate_extra_inputs(extra,prior))==887
for name in ['missing-extra','foreign-extra','nonstandard-extra','overlap-extra']:
 bad=copy.deepcopy(extra);key=next(iter(bad))
 if name=='missing-extra':bad.pop(key)
 elif name=='foreign-extra':bad['Solidity.Lowering.V08.Other.fake']=bad.pop(key)
 elif name=='nonstandard-extra':bad[key]=['sorryAx']
 else:bad[next(iter(prior))]=bad.pop(key)
 try:module.validate_extra_inputs(bad,prior)
 except AssertionError:pass
 else:raise AssertionError('accepted '+name)
print('PASS:81 case intents total (one evidence positive/80 negatives), plus descriptor/base/combined-inventory positives')
