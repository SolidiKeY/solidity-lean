#!/usr/bin/env python3
"""Clean serial Lake closure gate in a 12 GiB, no-swap, one-CPU container.
Bulk logs and sampled aggregate process RSS remain outside Git.
"""
import fcntl, hashlib, json, os, pathlib, re, signal, subprocess, sys, time
from bulk import load_bulk_json
ROOT=pathlib.Path(__file__).resolve().parents[4]
E=pathlib.Path('/workspace/migrate-optimizer-evidence')
if load_bulk_json('measurements.json').get('performance_status')=='STOP_GT_10_PERCENT':
 raise SystemExit('STOP_GT_10_PERCENT: root-gate disposition required before further Lean validation')
D=['env','-u','DOCKER_HOST','-u','DOCKER_CONTEXT','-u','DOCKER_TLS','-u','DOCKER_TLS_VERIFY','-u','DOCKER_CERT_PATH','docker','--host=unix:///var/run/docker.sock']
VERSION=sys.argv[1]; assert VERSION in ['4.24.0','4.35.0']
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=ROOT).strip()
RUN=sys.argv[2] if len(sys.argv)>2 else 'clean-'+VERSION
assert re.fullmatch(r'[A-Za-z0-9.-]+',RUN)
name='h62-migrate-optimizer-'+RUN
MODE=sys.argv[3] if len(sys.argv)>3 else 'closure'
if MODE in ['isolated','generic']:
 raise SystemExit('H112: copied-definition modes are historical only; use real-module closure/audit-old after hold disposition')
assert MODE in ['closure','audit-old']
assert MODE!='audit-old' or VERSION=='4.24.0'
run=E/RUN;run.mkdir(exist_ok=False)
for proc in pathlib.Path('/proc').iterdir():
 if proc.name.isdigit():
  try: assert (proc/'comm').read_text().strip() not in ['lean','lake'], 'existing Lean/Lake process '+proc.name
  except FileNotFoundError: pass
assert len(pathlib.Path('/proc/swaps').read_text().splitlines())==1
cgroup=pathlib.Path('/sys/fs/cgroup')
def available():
 host=next(int(x.split()[1])*1024 for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
 return min(host,int((cgroup/'memory.max').read_text())-int((cgroup/'memory.current').read_text()))
assert available()>4*1024**3
pin=json.loads(pathlib.Path('/workspace/h62-coordinator-inputs/toolchain-pin.json').read_text())
archive=E/'toolchains'/('lean-'+VERSION+'-linux.tar.zst')
sha=hashlib.file_digest(archive.open('rb'),'sha256').hexdigest()
if VERSION=='4.35.0':assert sha==pin['sha256']
x=load_bulk_json('census.json')
# The scope files and dependency source hashes must still match the frozen census.
for f in x['files'].values():
 assert hashlib.sha256((ROOT/f['path']).read_bytes()).hexdigest()==f['sha256']
 original=subprocess.check_output(['git','show','c6f550e281a7e5affa9a99bc2cdaed556dec00e4:'+f['path']],cwd=ROOT)
 assert hashlib.sha256(original).hexdigest()==f['sha256'], 'census differs from pinned base'
config=(ROOT/'lakefile.toml').read_text().replace('enableArtifactCache = true','enableArtifactCache = false').replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]')
config=config.replace('srcDir = "vendor/LeanTeX"','srcDir = "/repo/vendor/LeanTeX"')
config=config.replace('version = "0.1.0"','version = "0.1.0"\nsrcDir = "/repo"\nbuildDir = "/evidence/'+RUN+'/build"')
# Executables also need explicit single-thread Lean, even though this gate builds module oleans only.
config=config.replace('[[lean_exe]]','[[lean_exe]]\nweakLeanArgs = ["--tstack=131072", "-j1"]')
if MODE=='audit-old': config=config.replace('/evidence/'+RUN+'/build','/evidence/reviewed-old/build')
(run/'runtime.toml').write_text(config)
lines=['set -eu','export PATH=/toolchain/bin:$PATH','export LEAN_NUM_THREADS=1','lean --version','lake --version']
ordered=x['ordered_closure']
if MODE=='audit-old': ordered=[]
for m in ordered:
 lines+=['echo TARGET='+m,'lake -d /repo -f /evidence/'+RUN+'/runtime.toml --no-cache build +'+m+':olean']
fixtures=['Interfaces.lean','Acceptance.lean'] if MODE=='audit-old' else []
for fixture in fixtures:
 lines+=['echo FIXTURE='+fixture,'lake -d /repo -f /evidence/'+RUN+'/runtime.toml env lean --tstack=131072 -j1 /repo/tests/h62/item6/migrate-optimizer/'+fixture]
(run/'build.sh').write_text('\n'.join(lines)+'\n')
image=subprocess.check_output(D+['image','inspect','ubuntu:24.04','--format','{{.Id}}'],text=True).strip()
cmd=D+['run','--cidfile',str(run/'container.cid'),'--name',name,'--network=none','--memory=12g','--memory-swap=12g','--cpus=1','--pids-limit=128','--mount','type=bind,src='+str(ROOT)+',dst=/repo,readonly','--mount','type=bind,src='+str(E)+',dst=/evidence','--mount','type=bind,src='+str(E/'toolchains'/('lean-'+VERSION+'-linux'))+',dst=/toolchain,readonly','--workdir','/repo',image,'/evidence/wait-usage','/evidence/'+RUN+'/usage.json','bash','/evidence/'+RUN+'/build.sh']
(run/'command.json').write_text(json.dumps(cmd,indent=2))
start=time.monotonic();samples=[];peak=0;reason=None
p=None; exitcode=125
def interrupted(signum, frame): raise RuntimeError('controller signal '+str(signum))
for sig in [signal.SIGINT,signal.SIGTERM]: signal.signal(sig,interrupted)
try:
 with (run/'build.log').open('w') as log:
  p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT)
  while p.poll() is None:
   top=subprocess.run(D+['top',name,'-eo','pid,comm,rss'],text=True,capture_output=True,timeout=10)
   if top.returncode==0:
    rows=[r.split() for r in top.stdout.splitlines()[1:]]
    rss=sum(int(r[-1])*1024 for r in rows);peak=max(peak,rss)
    samples.append({'seconds':time.monotonic()-start,'aggregate_rss':rss,'processes':rows,'available':available()})
    assert len([r for r in rows if r[1]=='lean'])<=1, 'competing Lean processes'
    assert rss<=12*1024**3 and available()>=4*1024**3, 'resource guard'
   assert time.monotonic()-start<=3600, '3600s wall guard'
   time.sleep(.5)
  exitcode=p.wait()
  assert samples, 'no successful resource-monitor samples'
except BaseException as error:
 reason=type(error).__name__+': '+str(error)
finally:
 # The CID file is created by Docker only for this invocation. A name conflict
 # must never cause cleanup to kill another invocation's container.
 cid=(run/'container.cid').read_text().strip() if (run/'container.cid').exists() else None
 if cid:
  assert re.fullmatch(r'[a-f0-9]{64}',cid)
  status=subprocess.run(D+['inspect','--format','{{.State.Running}}',cid],text=True,capture_output=True,timeout=10)
  if status.returncode==0 and status.stdout.strip()=='true':
   subprocess.run(D+['kill',cid],capture_output=True,timeout=15,check=True)
 if p is not None: exitcode=p.wait(timeout=15)
wall=time.monotonic()-start
inspect=subprocess.run(D+['inspect',name],text=True,capture_output=True)
(run/'container.json').write_text(inspect.stdout)
(run/'samples.json').write_text(json.dumps(samples))
result={'version':VERSION,'archive_sha256':sha,'image':image,'exit':exitcode,'wall_seconds':wall,'peak_sampled_aggregate_rss_bytes':peak,'rss_sampling_seconds':.5,'reason':reason,'targets':x['targets'],'mode':MODE,'ordered_modules':ordered,'fixtures':fixtures,'scope':{'closure':'Clean KeySort prerequisite, local transitive imports and four assigned modules; not full run-lean final gate','audit-old':'Full old-toolchain interface and acceptance fixtures using reviewed-old artifacts; warm audit, not a clean build'}[MODE]}
if (run/'usage.json').exists(): result['kernel_usage']=json.loads((run/'usage.json').read_text())
(run/'result.json').write_text(json.dumps(result,indent=2));print(json.dumps(result),flush=True)
sys.exit(exitcode if not reason else 125)
