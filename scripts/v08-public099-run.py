import pathlib,json,hashlib,http.client,socket,time,os,fcntl,subprocess,re,signal,sys
R=pathlib.Path(sys.argv[1]).resolve();assert R.is_dir();ROOT=pathlib.Path('/workspace/v08-world-lowering-public099');OLD=pathlib.Path('/workspace/v08-world-lowering-published');P=pathlib.Path('/workspace/v08-world-lowering-artifacts/published-099-runtime-proposal-20261101')
PROPOSAL=P/'runtime-proposal.json';MODEL=json.loads(PROPOSAL.read_bytes());NAME=MODEL['proposed_container_name'];TOKEN=MODEL['planned_run_token'];PROFILE=json.loads(json.dumps(MODEL['proposed_additional_same_VM_runtime_profile']));PREPARED_PROFILE_SHA=hashlib.sha256(json.dumps(PROFILE,sort_keys=True).encode()).hexdigest();PROFILE['Cmd']=['timeout','--signal=KILL','600',*PROFILE['Cmd']];DEADLINE=None;LIMIT=12884901888;RESERVE=540000000
H=lambda b:hashlib.sha256(b).hexdigest()
def digest(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(65536),b''):h.update(b)
 return h.hexdigest()
def put(n,x):
 p=R/n;assert not p.exists(),('preserve prior record',n);p.write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
class C(http.client.HTTPConnection):
 def connect(self):self.sock=socket.socket(socket.AF_UNIX,socket.SOCK_STREAM);self.sock.settimeout(self.timeout);self.sock.connect('/var/run/docker.sock')
def api(method,path,data=None,timeout=30,cleanup=False):
 if DEADLINE is not None and not cleanup:
  remaining=DEADLINE-time.monotonic()
  if remaining<=0:raise TimeoutError('original600s_wall_guard')
  timeout=min(timeout,remaining)
 c=C('localhost',timeout=timeout);c.request(method,path,body=None if data is None else json.dumps(data).encode(),headers={} if data is None else {'Content-Type':'application/json'});r=c.getresponse();b=r.read();status=r.status;c.close();return status,b

def get(path):
 s,b=api('GET',path);assert s==200,(s,path);return json.loads(b)
def free():return os.statvfs('/workspace').f_bavail*os.statvfs('/workspace').f_frsize
def git(root,*args):return subprocess.check_output(['git','--no-optional-locks','-C',str(root),*args]).decode().strip()
def seal(directory,expected):
 p=pathlib.Path(directory)/'SHA256SUMS';assert digest(p)==expected
 count=0
 for line in p.read_text().splitlines():
  sha,name=line[:64],line[66:];assert digest(p.parent/name)==sha,name;count+=1
 return count

def fingerprint(root):
 names=subprocess.check_output(['git','--no-optional-locks','-C',str(root),'ls-files','-z','--cached','--others','--exclude-standard','*.lean','lean-toolchain','lakefile.toml'],text=True).split('\0')
 return {n:digest(root/n) for n in sorted(set(names)-{''}) if (root/n).is_file()}
def norm_inspect(j):
 j=dict(j);j['Mounts']=sorted(j.get('Mounts',[]),key=lambda x:json.dumps(x,sort_keys=True));return H(json.dumps(j,sort_keys=True).encode())
def protected(ids):return {cid:norm_inspect(get('/containers/'+cid+'/json')) for cid in ids}
def idle():
 active=[];unread=[]
 for p in pathlib.Path('/proc').iterdir():
  if not p.name.isdigit() or int(p.name)==os.getpid():continue
  try:cmd=(p/'cmdline').read_bytes();comm=(p/'comm').read_text().strip()
  except (FileNotFoundError,ProcessLookupError):continue
  except PermissionError:unread.append(p.name);continue
  if comm in ['lean','lake'] or b'v08-reuse-' in cmd or b'v08-bounded.py' in cmd:active.append({'pid':p.name,'comm':comm,'cmd_sha256':H(cmd)})
 assert not active and not unread,('competing/uninspectable build',active,unread)
 return {'active':active,'unreadable':unread}
lease=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','r+');fcntl.flock(lease,fcntl.LOCK_EX|fcntl.LOCK_NB)
marker=R/'operation-started.json';assert not marker.exists(),'one-shot creation/start; inspect existing journal instead of retry'
assert git(OLD,'rev-parse','HEAD')=='7c3c8274eeafe908a1e96709d0491c02b306e03f' and not git(OLD,'status','--porcelain')
assert git(ROOT,'rev-parse','HEAD')=='099bfbe185731c354b12a40f28ccf5d98534c779'
assert git(ROOT,'merge-base','099bfbe185731c354b12a40f28ccf5d98534c779','fb379ae20f10e2c92113453ddd9d40d8f2efbe09')=='fb379ae20f10e2c92113453ddd9d40d8f2efbe09'
assert seal('/workspace/v08-world-lowering-artifacts/checkpoint-source-transient-20261101','a74444aab536774e32f6b45e0011458a4f8b1f9359aba8aa2749ab263ef31d17')==12
assert seal(P,'4d52b18458d7a0e9b3d346af747661172e9142869af1bff46ccddb63353c4d9a')==11
# Published ownership is checked against the exact incoming public revision.
for path in ['Solidity.lean','docs/module-map.md','docs/README.md']:
 incoming=subprocess.check_output(['git','show',MODEL['new_public_base']+':'+path],cwd=ROOT)
 assert (ROOT/path).read_bytes().startswith(incoming),('not append-only',path)
changed=set(git(ROOT,'diff','--name-only',MODEL['new_public_base']).splitlines())
changed.update(git(ROOT,'ls-files','--others','--exclude-standard').splitlines())
for path in changed:
 assert path.startswith(('Solidity/Lowering/V08/','scripts/v08-')) or path in ['Solidity.lean','docs/module-map.md','docs/README.md','docs/feature-work/roadmap-v08-world-lowering.md'],('ownership',path)
first=pathlib.Path('/workspace/v08-world-lowering-evidence/public099-validation-20261101')
cold_provenance=json.loads((first/'result.json').read_bytes())
assert cold_provenance['exit']==125 and cold_provenance['guard_stop']=='original600s_wall_guard'
assert cold_provenance['source_unchanged'] and cold_provenance['old_containers_unchanged'] and cold_provenance['cleanup_verified']
assert digest(first/'build.log')==cold_provenance['log_sha256'] and digest(first/'docker-logs.raw')==cold_provenance['raw_log_sha256']
previous=pathlib.Path(sys.argv[2]).resolve() if len(sys.argv)>2 else first
prior=json.loads((previous/'result.json').read_bytes())
assert prior['exit'] in [0,1,125]
assert prior['source_unchanged'] and prior['old_containers_unchanged'] and prior['cleanup_verified']
assert digest(previous/'build.log')==prior['log_sha256'] and digest(previous/'docker-logs.raw')==prior['raw_log_sha256']
assert 'error:' not in (first/'build.log').read_text()
CID=prior['container_id'];assert CID=='47c5808627ffeadf7d11884f8c37dd554eae2ed7bc5d55756781500b6ecf9a20'
# Nonpassing cold-prefix provenance, not a passing closure certificate.
cutoff=(previous/'result.json').stat().st_mtime_ns
warm={};cold=[]
for module in MODEL['source_config']['ordered_serial_modules']:
 rel=pathlib.Path(module.replace('.','/'));name=str(rel.with_suffix('.lean'))
 if digest(ROOT/name)!=prior['source_sha256'][name]:cold.append(module);continue
 lib=ROOT/'.lake/build/lib/lean'/rel;ir=ROOT/'.lake/build/ir'/rel
 files=[lib.with_suffix(ext) for ext in ['.olean','.olean.hash','.ilean','.ilean.hash','.trace']]
 files += [ir.with_suffix(ext) for ext in ['.c','.c.hash','.setup.json']]
 if not all(p.is_file() for p in files):cold.append(module);continue
 trace=json.loads(lib.with_suffix('.trace').read_text())
 assert trace['outputs']['o']==[lib.with_suffix('.olean.hash').read_text().strip()]
 assert trace['outputs']['i']==lib.with_suffix('.ilean.hash').read_text().strip()
 assert trace['outputs']['c']==ir.with_suffix('.c.hash').read_text().strip()
 metadata={}
 for artifact in files:
  stat=artifact.stat();assert stat.st_ctime_ns<=cutoff,('output changed after cold-prefix record',artifact)
  metadata[str(artifact)]=dict(bytes=stat.st_size,ctime_ns=stat.st_ctime_ns,sha256=digest(artifact))
 warm[module]=dict(source_sha256=digest(ROOT/name),artifacts=metadata)
assert len(warm)>=100,('cold prefix not demonstrably cached',len(warm))
assert fingerprint(ROOT)!=prior['source_sha256'] or previous==first or (prior['guard_stop']=='original600s_wall_guard' and len(warm)>len(json.loads((previous/'warm-prefix.json').read_bytes())['warm'])), 'no source change or measured cache progress; unchanged retry rejected'
put('warm-prefix.json',dict(previous_result=str(previous/'result.json'),prior_sha256=digest(previous/'result.json'),warm=warm,cold=cold,prior_exit=prior['exit'],no_cache_copy=True))
assert digest(MODEL['source_config']['path'])==MODEL['source_config']['sha256']
assert PROFILE['HostConfig']['Memory']==PROFILE['HostConfig']['MemorySwap']==LIMIT and PROFILE['HostConfig']['NanoCpus']==1000000000 and PROFILE['HostConfig']['NetworkMode']=='none'
assert set(PROFILE['Env'])=={'LEAN_NUM_THREADS=1','LAKE_CACHE_DIR=','LAKE_ARTIFACT_CACHE=false'}
assert PROFILE['WorkingDir']==str(ROOT) and PROFILE['User']==str(os.getuid())+':'+str(os.getgid()) and PROFILE['Labels']['org.solidity.v08.run']==TOKEN
assert 'prune' not in PROFILE['Cmd'][-1] and ' build Solidity.KeySort;' in PROFILE['Cmd'][-1]
assert pathlib.Path('/sys/fs/cgroup/memory.max').read_text().strip()=='17179869184'
assert len(pathlib.Path('/proc/swaps').read_text().splitlines())==1
assert free()>RESERVE+MODEL['allocation_forecast']['total_estimate']
assert int(pathlib.Path('/sys/fs/cgroup/memory.current').read_text())<12*1024**3
idle_check=idle();before_list=get('/containers/json?all=1');assert all(c['State'] not in ['running','paused','restarting'] for c in before_list)
assert len([c for c in before_list if c['Id']==CID])==1
old_ids=[c['Id'] for c in before_list if c['Id']!=CID];old_meta=protected(old_ids)
assert old_meta==json.loads((first/'preflight.json').read_bytes())['protected_container_hashes']
image=get('/images/'+PROFILE['Image']+'/json');assert image['Id']==get('/containers/0fe0539b0be4c295d0e2d75ca6523b80c44e00e15e6322211ccb02a19617a6ba/json')['Image']
s,b=api('GET','/containers/'+NAME+'/json');assert s==200 and json.loads(b)['Id']==CID,'exact existing runtime required; never create'
status,log_prefix=api('GET','/containers/'+CID+'/logs?stdout=1&stderr=1&timestamps=0');assert status==200
prior_cumulative=previous/'docker-logs.cumulative.raw'
if prior_cumulative.exists():
 assert digest(prior_cumulative)==prior['cumulative_raw_log_sha256']
else:prior_cumulative=previous/'docker-logs.raw'
assert log_prefix==prior_cumulative.read_bytes(), 'cumulative log drift before start'
put('log-boundary.json',dict(previous_raw=str(prior_cumulative),sha256=H(log_prefix),bytes=len(log_prefix),previous_result=str(previous/'result.json'),previous_result_sha256=digest(previous/'result.json')))
source_before=fingerprint(ROOT);old_source=fingerprint(OLD);config_sha=digest(MODEL['source_config']['path']);disk_before=free()
put('preflight.json',{'old_head':git(OLD,'rev-parse','HEAD'),'new_base':git(ROOT,'rev-parse','HEAD'),'source_before':source_before,'old_source':old_source,'protected_container_hashes':old_meta,'image':image['Id'],'disk_before':disk_before,'parent_memory_current':int(pathlib.Path('/sys/fs/cgroup/memory.current').read_text()),'idle':idle_check,'config_sha256':config_sha})
put('operation-started.json',{'intent':'REUSE ONLY exact existing stopped application container; cold outputs measured, new owned source application; no creation','name':NAME,'token':TOKEN,'profile':PROFILE,'profile_sha256':H(json.dumps(PROFILE,sort_keys=True).encode()),'prepared_profile_sha256':PREPARED_PROFILE_SHA,'inner_timeout_seconds':600,'controller_sha256':digest(__file__),'proposal_sha256':digest(PROPOSAL),'pid':os.getpid(),'no_retries_after_uncertainty':True})
j=get('/containers/'+CID+'/json');cid=j['Id'];assert cid==CID and j['Name']=='/'+NAME and j['Config']['Labels']['org.solidity.v08.run']==TOKEN
assert j['HostConfig']['Memory']==j['HostConfig']['MemorySwap']==LIMIT and j['HostConfig']['NanoCpus']==1000000000 and j['HostConfig']['NetworkMode']=='none'
assert j['Config']['Cmd']==PROFILE['Cmd'] and j['Config']['WorkingDir']==str(ROOT) and not j['State']['Running']
assert j['Image']==image['Id'] and j['Config']['User']==PROFILE['User']
expected_env=dict(v.split('=',1) for v in image.get('Config',{}).get('Env',[]));expected_env.update(dict(v.split('=',1) for v in PROFILE['Env']));assert dict(v.split('=',1) for v in j['Config']['Env'])==expected_env
assert not j['HostConfig'].get('Privileged',False) and not j['HostConfig'].get('PidMode')
expected_mounts={x.split(':')[1]:(x.split(':')[0],not x.endswith(':ro')) for x in PROFILE['HostConfig']['Binds']}
assert {m['Destination']:(m['Source'],m['RW']) for m in j['Mounts']}==expected_mounts
assert free()>RESERVE+536870912+67108864,'reuse disk admission fails; keep stopped container'
put('reused-id.json',{'id':cid,'name':NAME,'token':TOKEN,'profile_sha256':H(json.dumps(PROFILE,sort_keys=True).encode()),'image_id':j['Image'],'mounts':j['Mounts'],'state':j['State'],'free_after_create':free(),'prestart_disk_delta':disk_before-free(),'no_create_request':True})
assert protected(old_ids)==old_meta,'existing container drift before start'
start=time.monotonic();DEADLINE=start+600
put('start-intent.json',{'id':cid,'time':time.time(),'wall_limit_seconds':600,'independent_inner_timeout_seconds':600,'rss_limit':LIMIT,'OS_headroom_bytes':2*1024**3,'parent_headroom_bytes':2*1024**3,'disk_floor':RESERVE})
peak=0;peak_memory=0;samples=0;reason=None;monitor_error=None;cleanup_verified=False

def interrupted(signum,frame):
 global reason
 reason='original600s_wall_guard' if signum==signal.SIGALRM else 'monitor_interrupted_signal_'+str(signum)
 raise RuntimeError(reason)
for sig in [signal.SIGINT,signal.SIGTERM,signal.SIGALRM]:signal.signal(sig,interrupted)
signal.setitimer(signal.ITIMER_REAL,600)
try:
 try:
  s,b=api('POST','/containers/'+cid+'/start');start_reply={'status':s,'body':b.decode('utf-8','replace')}
 except Exception as ex:start_reply={'uncertain':True,'exception':type(ex).__name__}
 put('start-reply.json',start_reply)
 state=get('/containers/'+cid+'/json')['State'];assert state['Running'] or state['StartedAt']!='0001-01-01T00:00:00Z','start unresolved; no retry'
 with (R/'samples.jsonl').open('x') as samplesfile:
  while True:
   state=get('/containers/'+cid+'/json')['State']
   if not state['Running']:break
   s,b=api('GET','/containers/'+cid+'/top?ps_args=-eo%20pid,rss,comm');rss=0;leans=0
   if s==200:
    top=json.loads(b)
    for row in top.get('Processes',[]):
     rss+=int(row[1])*1024
     if row[2]=='lean':leans+=1
   else:raise RuntimeError('cannot inspect running process RSS')
   stats=get('/containers/'+cid+'/stats?stream=false');usage=stats.get('memory_stats',{}).get('usage',0)
   available=int(next(line.split()[1] for line in pathlib.Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')))*1024
   parent=int(pathlib.Path('/sys/fs/cgroup/memory.current').read_text());elapsed=time.monotonic()-start;space=free();peak=max(peak,rss);peak_memory=max(peak_memory,usage);samples+=1
   sample={'elapsed':elapsed,'rss':rss,'memory_usage':usage,'lean_processes':leans,'available':available,'parent_current':parent,'disk_available':space};samplesfile.write(json.dumps(sample)+'\n');samplesfile.flush()
   if elapsed>=600:reason='original600s_wall_guard'
   elif rss>LIMIT:reason='aggregate_RSS_guard'
   elif available<2*1024**3:reason='OS_headroom_guard'
   elif parent>14*1024**3:reason='parent_cgroup_headroom_guard'
   elif space<RESERVE:reason='original_disk_reserve_guard'
   elif leans>1:reason='serial_Lean_guard'
   if reason:
    put('guard-stop.json',{'reason':reason,'sample':sample,'own_id':cid});break
   time.sleep(min(.5,max(0,DEADLINE-time.monotonic())))
except BaseException as ex:
 monitor_error={'type':type(ex).__name__,'reason':reason or 'monitor_failure'}
 reason=reason or 'monitor_failure'
finally:
 for sig in [signal.SIGINT,signal.SIGTERM,signal.SIGALRM]:signal.signal(sig,signal.SIG_IGN)
 signal.setitimer(signal.ITIMER_REAL,0)
 # Exact created ID plus immutable ownership token; never touch another container.
 try:
  status,raw=api('GET','/containers/'+cid+'/json',timeout=5,cleanup=True);assert status==200
  owned=json.loads(raw);assert owned['Id']==cid and owned['Config']['Labels']['org.solidity.v08.run']==TOKEN
  cleanup={'id':cid,'owned_token_verified':True,'running_before':owned['State']['Running'],'monitor_error':monitor_error}
  if owned['State']['Running']:
   status,raw=api('POST','/containers/'+cid+'/stop?t=0',timeout=5,cleanup=True);cleanup['stop_reply']={'status':status,'body':raw.decode('utf-8','replace')}
  status,raw=api('GET','/containers/'+cid+'/json',timeout=5,cleanup=True);assert status==200
  final=json.loads(raw);cleanup_verified=not final['State']['Running'];cleanup['final_state']=final['State'];cleanup['verified_stopped']=cleanup_verified
  put('cleanup.json',cleanup)
 except BaseException as ex:
  cleanup_verified=False
  try:put('cleanup-unresolved.json',{'id':cid,'exception_type':type(ex).__name__,'no_delete_no_start_retry':True,'inner_timeout_still_bounds_process':True})
  except Exception:pass
DEADLINE=None
if not cleanup_verified:
 put('result.json',{'exit':125,'container_id':cid,'cleanup_verified':False,'monitor_error':monitor_error,'guard_stop':reason,'action':'read-only ID/state reconciliation required; never duplicate/create/start blindly'});raise SystemExit(125)
state=get('/containers/'+cid+'/json')['State']
s,b=api('GET','/containers/'+cid+'/logs?stdout=1&stderr=1&timestamps=0');assert s==200
cumulative_raw=b
assert b.startswith(log_prefix),'old cumulative log prefix changed; do not attribute to current run'
b=b[len(log_prefix):]
pos=0;parts=[]
while pos+8<=len(b):
 assert b[pos] in [0,1,2] and b[pos+1:pos+4]==b'\0\0\0';n=int.from_bytes(b[pos+4:pos+8],'big');pos+=8;assert pos+n<=len(b);parts.append(b[pos:pos+n]);pos+=n
assert pos==len(b);log=b''.join(parts)
secret_patterns=[rb'https?://[^\s/"]+:[^\s/@"]+@',rb'(?i)authorization[\s":]+(?:bearer|basic)\s+[A-Za-z0-9+/=_-]+',rb'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----',rb'\b(?:gh[pousr]_[A-Za-z0-9]{20,}|AKIA[A-Z0-9]{16})\b']
log_safe=not any(re.search(pattern,log) for pattern in secret_patterns)
if log_safe:
 (R/'docker-logs.cumulative.raw').write_bytes(cumulative_raw);(R/'docker-logs.raw').write_bytes(b);(R/'build.log').write_bytes(log)
else:put('log-withheld.json',{'reason':'credential-pattern hold; no values exported','raw_sha256':H(b),'decoded_sha256':H(log),'raw_bytes':len(b)})
source_after=fingerprint(ROOT);old_after=fingerprint(OLD);protected_after=protected(old_ids);unchanged=source_before==source_after and old_source==old_after and digest(MODEL['source_config']['path'])==config_sha
peaks=re.findall(rb'V08_CGROUP_PEAK=(\d+)',log)
versions=[line for line in log.decode('utf-8','replace').splitlines() if line.startswith(('Lean (version ','Lake version '))]
expected_versions=['Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)','Lake version 5.0.0-src+797c613 (Lean version 4.24.0)']
valid=unchanged and old_meta==protected_after and samples>0 and peak>0 and bool(peaks) and versions==expected_versions and log_safe and cleanup_verified
code=125 if reason or monitor_error or not valid else state['ExitCode']
result={'exit':code,'actual_container_exit':state['ExitCode'],'guard_stop':reason,'monitor_error':monitor_error,'cleanup_verified':cleanup_verified,'measurement_and_bindings_valid':valid,'container_id':cid,'name':NAME,'token':TOKEN,'source_unchanged':unchanged,'old_containers_unchanged':old_meta==protected_after,'old_head':git(OLD,'rev-parse','HEAD'),'candidate_base':git(ROOT,'rev-parse','HEAD'),'modules':MODEL['source_config']['ordered_serial_modules'],'source_sha256':source_after,'config_sha256':config_sha,'log':str(R/'build.log') if log_safe else None,'log_sha256':H(log),'raw_log_sha256':H(b),'cumulative_raw_log_sha256':H(cumulative_raw),'log_prefix_sha256':H(log_prefix),'tool_versions':versions,'wall_seconds':time.monotonic()-start,'samples':samples,'peak_aggregate_rss':peak,'peak_sampled_cgroup_usage':peak_memory,'cgroup_peak':int(peaks[-1]) if peaks else None,'disk_before':disk_before,'disk_after':free(),'no_new_goal_or_vm':True,'no_delete':True,'no_duplication':True,'independent_inner_timeout_seconds':600}
put('result.json',result)
print(json.dumps({k:result[k] for k in ['exit','actual_container_exit','guard_stop','container_id','wall_seconds','peak_aggregate_rss','cgroup_peak','disk_after','source_unchanged','old_containers_unchanged','cleanup_verified']}),flush=True)
raise SystemExit(0 if code==0 else 1)
