#!/usr/bin/env python3
"""Unmodified repository full gate, bounded and with serial actual Lean calls.
Only task-local configuration/wrappers are used; roots/registries stay untouched.
"""
import fcntl,hashlib,json,os,pathlib,shlex,subprocess,sys,time,tomllib,uuid
from resource_guard import available_bytes,heavy_lock
root=pathlib.Path(__file__).resolve().parents[3];area=root/'tests/h28-sol/type-grammar'
writer=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a');fcntl.flock(writer,fcntl.LOCK_EX|fcntl.LOCK_NB)
heavy=heavy_lock()
if available_bytes()<4*1024**3:raise SystemExit('Insufficient VM/host headroom')
env=os.environ.copy()
for k in ('DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH'):env.pop(k,None)
docker=['docker','--host=unix:///var/run/docker.sock']
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
mode=sys.argv[1] if len(sys.argv)>1 else 'full'
defaults=tomllib.loads((root/'lakefile.toml').read_text())['defaultTargets']
assert defaults==tomllib.loads((area/'runtime.toml').read_text())['defaultTargets']
commands={'full':['bash','scripts/coord-tools/gate.sh','full'],'build':['lake','build',*defaults,'SolkeyTestSuite'],'solkey':['bash','scripts/check-solkey.sh']}
if mode not in commands:raise SystemExit('unsupported validation mode')
validation_command=commands[mode]
name='h28-'+mode+'-'+uuid.uuid4().hex[:12];logs=area/'evidence'/name;logs.mkdir()
paths=set(subprocess.check_output(['git','ls-files','-co','--exclude-standard'],cwd=root,text=True).splitlines())
paths={p for p in paths if '/evidence/' not in p and (pathlib.Path(p).suffix in ('.lean','.py','.mjs','.sh','.toml','.sol','.g4','.json') or p.endswith('lean-toolchain'))}
paths.add('tests/h28-sol/type-grammar/final-bin/lake')
source_hashes={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sorted(paths)}
image='ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852'
python='/opt/codex/runtimes/codex-primary-runtime/dependencies/python'
cmd=docker+['run','--name',name,'--network','none','--memory','12g','--memory-swap','12g','--cpus','1','--user','1000:1000']
mounts=[(str(root),str(root),False),('/workspace/.setup/tools/lean-4.24.0-linux','/opt/lean',True),('/workspace/.setup/cache/lake','/workspace/.setup/cache/lake',False),(python,python,True),('/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin/node','/usr/bin/node',True),('/usr/bin/git','/usr/bin/git',True),('/lib/x86_64-linux-gnu/libpcre2-8.so.0','/lib/x86_64-linux-gnu/libpcre2-8.so.0',True),('/lib/x86_64-linux-gnu/libz.so.1','/lib/x86_64-linux-gnu/libz.so.1',True),('/workspace/.setup/solkey','/workspace/.setup/solkey',True),(str(root/'tests/migration/solkey.pin.json'),'/workspace/.setup/solkey.pin.json',True)]
for source,target,readonly in mounts:cmd+=['--mount','type=bind,src='+source+',dst='+target+(',readonly' if readonly else '')]
cmd+=['-w',str(root)]
settings={'LEAN_NUM_THREADS':'1','LAKE_CACHE_DIR':'/workspace/.setup/cache/lake','PATH':str(area/'final-bin')+':'+python+'/bin:/opt/lean/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin','GATE_BASE':'6f3eedf0788ee1f8a3bcf230558c712ecdca04d5','GATE_LOGS':str(logs),'SOLKEY_EXAMPLES':'/workspace/.setup/solkey/keyext.solidity.examples','SOLKEY_RULES':'/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key','NODE_OPTIONS':'--max-old-space-size=4096','GIT_CONFIG_GLOBAL':'/dev/null','GIT_CONFIG_NOSYSTEM':'1'}
for k,v in settings.items():cmd+=['-e',k+'='+v]
script='set -eu; test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888; test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0; git --version; python3 --version; node --version; lean --version; lake --version; set +e; '+shlex.join(validation_command)+'; h28_gate_status=$?; printf CGROUP_PEAK=; cat /sys/fs/cgroup/memory.peak; exit "$h28_gate_status"'
cmd+=[image,'sh','-c',script]
start=time.monotonic();peak_rss=0;minimum=available_bytes();guard=None;stages={}
with (logs/'outer.log').open('w') as output:
 output.write(json.dumps(cmd)+'\n');output.flush();proc=subprocess.Popen(cmd,env=env,stdout=output,stderr=subprocess.STDOUT)
 try:
  while proc.poll() is None:
   sample=subprocess.run(docker+['top',name,'-eo','pid,rss'],env=env,capture_output=True,text=True)
   if sample.returncode==0:
    rss=sum(int(line.split()[1])*1024 for line in sample.stdout.splitlines()[1:] if len(line.split())==2);peak_rss=max(peak_rss,rss)
    active=[int(p.stem) for p in logs.glob('*.log') if p.stem.isdigit()]
    if active:stages[str(max(active))]=max(stages.get(str(max(active)),0),rss)
   minimum=min(minimum,available_bytes())
   if minimum<4*1024**3 or time.monotonic()-start>600:
    guard='HEADROOM_OR_600S_GUARD';subprocess.run(docker+['stop','-t','5',name],env=env,capture_output=True);break
   time.sleep(.5)
  code=proc.wait(timeout=15)
 except BaseException:
  subprocess.run(docker+['stop','-t','5',name],env=env,capture_output=True);raise
inspect=subprocess.run(docker+['inspect','--format','{{.HostConfig.Memory}} {{.HostConfig.MemorySwap}} {{.State.OOMKilled}} {{.State.ExitCode}}',name],env=env,capture_output=True,text=True)
unchanged=all(hashlib.sha256((root/p).read_bytes()).hexdigest()==h for p,h in source_hashes.items())
if not unchanged:guard='SOURCE_CHANGED_DURING_GATE'
rows=[]
if (logs/'gates.tsv').exists():
 for index,line in enumerate((logs/'gates.tsv').read_text().splitlines(),1):
  status,label,seconds,evidence,command=line.split('\t',4);rows.append(dict(status=status,gate=label,elapsed_s=int(seconds),evidence=evidence,command=command,sampled_container_peak_rss_bytes=stages.get(str(index))))
result=dict(head=head,branch=subprocess.check_output(['git','branch','--show-current'],cwd=root,text=True).strip(),repository=str(root),command=cmd,policy_command=validation_command,mode=mode,exit=code,guard=guard,elapsed_s=time.monotonic()-start,sampled_peak_rss_bytes=peak_rss or None,minimum_vm_or_host_headroom_bytes=minimum,limits=inspect.stdout.strip(),source_hashes=source_hashes,source_unchanged=unchanged,gates=rows,logs=str(logs))
(logs/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('source_hashes','command')}))
raise SystemExit(1 if guard or code else 0)
