#!/usr/bin/env python3
"""In-memory corruption tests against actual H1 evidence; never alter sealed files."""
import importlib.util,json,pathlib,sys,unittest.mock as mock
sys.dont_write_bytecode=True
root=pathlib.Path(sys.argv[1]);run=pathlib.Path(sys.argv[2])
spec=importlib.util.spec_from_file_location('guard',root/'scripts/v08-check-h1.py');guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
assert sys.argv[3:] in [[],['--suite']]
component='suite' if sys.argv[3:] else 'owned'
positive=guard.validate(root,run,component)
assert positive['component']=='SolkeyTestSuite' if component=='suite' else positive['pins']==1217
read_bytes=pathlib.Path.read_bytes;read_text=pathlib.Path.read_text
cases=[]
def corrupt(path,value,label):cases.append((path,value,label))
def mutate(name,fn,label):
 p=run/name;d=json.loads(read_text(p));fn(d);corrupt(p,json.dumps(d).encode(),label)
mutate('result.json',lambda d:d.update(exit=125),'failed-gate')
mutate('result.json',lambda d:d.update(source_and_controls_checked=False),'unbound-source')
mutate('result.json',lambda d:d.update(minimum_free_ram=4294967295),'ram-reserve')
mutate('result.json',lambda d:d.update(peak_aggregate_rss=12884901889),'memory-cap')
mutate('result.json',lambda d:d.update(cleanup_stopped=False),'not-stopped')
mutate('before.json',lambda d:d['profile']['HostConfig'].update(MemorySwap=12884901889),'swap')
mutate('before.json',lambda d:d['profile']['HostConfig'].update(NanoCpus=2000000000),'cpu')
mutate('before.json',lambda d:d['profile']['Cmd'].__setitem__(2,'601'),'wall')
mutate('before.json',lambda d:d['profile']['Env'].__setitem__(1,'LAKE_CACHE_DIR=/cache'),'artifact-cache')
mutate('before.json',lambda d:d.update(disk=499999999),'disk-admission')
corrupt(run/'samples.jsonl',b'', 'missing-samples')
corrupt(run/'raw.log',read_bytes(run/'raw.log')+b'X','raw-log')
corrupt(run/'build.log',read_bytes(run/'build.log')+b'X','decoded-log')
corrupt(root/'Solidity/Lowering/V08/SourceTransientZeroPayment.lean',b'changed','source')
corrupt(root/'scripts/v08-h1-check.sh',b'changed','runner-control')
p=root/'scripts/v08-h1-axiom-pins.json';d=json.loads(read_text(p));d[next(iter(d))]=['sorryAx'];corrupt(p,json.dumps(d).encode(),'axiom-set')
mutate('before.json',lambda d:d['source'].pop(next(iter(d['source']))),'source-inventory-omission')
mutate('before.json',lambda d:d['controls'].pop(next(iter(d['controls']))),'control-inventory-omission')
mutate('before.json',lambda d:d['profile']['Cmd'].append('ignored'),'command-suffix')
mutate('result.json',lambda d:d.update(peak_aggregate_rss=d['peak_aggregate_rss']+1),'rss-extrema')
mutate('runtime-after.json',lambda d:d.update(Image='sha256:wrong'),'image')
mutate('runtime-after.json',lambda d:d['Config']['Labels'].update({'org.solidity.v08.h1.token':'wrong'}),'runtime-token')
mutate('runtime-after.json',lambda d:d['Mounts'][0].update(RW=not d['Mounts'][0]['RW']),'mount')
mutate('runtime-after.json',lambda d:d['HostConfig'].update(Privileged=True),'privileged')
mutate('runtime-after.json',lambda d:d['Config']['Env'].remove('LEAN_NUM_THREADS=1'),'actual-env')
mutate('log-bindings.json',lambda d:d.update(cumulative_sha256='0'*64),'cumulative-log')
corrupt(run/'prefix.raw',read_bytes(run/'prefix.raw')+b'X','prefix-log')
p=run/'samples.jsonl';rows=[json.loads(x) for x in read_text(p).splitlines()];rows[0]['elapsed']=601
corrupt(p,('\n'.join(json.dumps(x) for x in rows)+'\n').encode(),'wall-sample')
p=run/'build.log';value=read_bytes(p).replace(b'H1_TARGET=Solidity.Source.Syntax',b'H1_TARGET=Solidity.Source.Wrong')
corrupt(p,value,'target-order')
mutate('runtime-after.json',lambda d:d['Config'].update(User='0:0'),'actual-user')
mutate('runtime-after.json',lambda d:d['Config'].update(WorkingDir='/tmp'),'actual-workingdir')
mutate('runtime-after.json',lambda d:d['Config']['Env'].append('LEAN_NUM_THREADS=2'),'extra-env')
mutate('runtime-after.json',lambda d:d.update(Name='/wrong'),'actual-name')
mutate('before.json',lambda d:d['profile']['HostConfig']['Binds'].append('/tmp:/tmp'),'unapproved-bind')
mutate('invocation-window.json',lambda d:d.update(since='0.0'),'shifted-log-since')
mutate('invocation-window.json',lambda d:d.update(container='wrong'),'window-container')
mutate('invocation-window.json',lambda d:d.update(started_at='1970-01-01T00:00:00.000000000Z'),'window-start')
mutate('invocation-window.json',lambda d:d.update(previous_finished_at='2099-01-01T00:00:00.000000000Z'),'window-finish')
mutate('invocation-window.json',lambda d:d.update(scope='tail-only'),'window-scope')
mutate('log-bindings.json',lambda d:d.update(query='tail=1'),'log-query')
mutate('before.json',lambda d:d.update(log_mode='cumulative'),'log-mode')
mutate('requested-targets.json',lambda d:d.update(mode='wrong'),'wrong-component-mode')
mutate('requested-targets.json',lambda d:d.update(requested=['Solidity.KeySort']),'omitted-component-root')
for path,value,label in cases:
 if component=='suite' and label=='axiom-set':continue
 def rb(p):return value if p==path else read_bytes(p)
 def rt(p,*a,**k):return value.decode() if p==path else read_text(p,*a,**k)
 with mock.patch.object(pathlib.Path,'read_bytes',rb),mock.patch.object(pathlib.Path,'read_text',rt):
  try:guard.validate(root,run,component)
  except (AssertionError,ValueError,KeyError):pass
  else:raise AssertionError('corruption accepted: '+label)
print(json.dumps({'positive':1,'corruptions_rejected':len(cases)-(1 if component=='suite' else 0),'labels':[x[2] for x in cases]}))
