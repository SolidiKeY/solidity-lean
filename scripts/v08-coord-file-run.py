#!/usr/bin/env python3
"""Additive complete console capture; same reviewed H1 runner and all old guards."""
import calendar,datetime
import os,sys,time,json,socket,http.client,pathlib,hashlib,fcntl,signal,uuid,importlib.util,re,tomllib,subprocess
ROOT=pathlib.Path('/workspace/v08-world-lowering-published');E=pathlib.Path('/workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102')
LIMIT=12884901888;RAM_RESERVE=4294967296;WALL=600;DEADLINE=None
NAME='v08-integrated-validation-20261102';TOKEN_FILE=E/'runtime-token.json';ACTIVE_OUT=None
class C(http.client.HTTPConnection):
 def connect(self):self.sock=socket.socket(socket.AF_UNIX);self.sock.settimeout(self.timeout);self.sock.connect('/var/run/docker.sock')
def api(method,path,data=None,cleanup=False):
 timeout=5 if cleanup else 15
 if DEADLINE is not None and not cleanup:
  remaining=DEADLINE-time.monotonic()
  if remaining<=0:raise TimeoutError('600s wall guard')
  timeout=min(timeout,remaining)
 c=C('localhost',timeout=timeout);c.request(method,path,None if data is None else json.dumps(data).encode(),{} if data is None else {'Content-Type':'application/json'});res=c.getresponse();b=res.read(32*1024**2+1);status=res.status;c.close()
 if len(b)>32*1024**2:
  record={'path':path,'status':status,'captured_bytes':len(b),'limit':32*1024**2,'sha256':hashlib.sha256(b).hexdigest(),'complete':False}
  if ACTIVE_OUT:
   put(ACTIVE_OUT/('api-overflow-'+str(time.time_ns())+'.json'),record)
   secret_free(b.decode(errors='replace'));(ACTIVE_OUT/('api-overflow-'+str(time.time_ns())+'.partial')).write_bytes(b)
  raise RuntimeError('bounded API/log response overflow; incomplete evidence')
 return status,b

def log_since(started_at):
 whole,fraction=started_at[:-1].split('.')
 return str(calendar.timegm(datetime.datetime.fromisoformat(whole).timetuple()))+'.'+fraction

def get(path,cleanup=False):
 s,b=api('GET',path,cleanup=cleanup);assert s==200,(s,path,b[:80]);return json.loads(b)
def put(p,x):assert not p.exists(),str(p);p.write_text(json.dumps(x,indent=2))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def disk():return os.statvfs('/workspace').f_bavail*os.statvfs('/workspace').f_frsize
def free_ram():
 a=next(int(x.split()[1])*1024 for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
 return min(a,int(pathlib.Path('/sys/fs/cgroup/memory.max').read_text())-int(pathlib.Path('/sys/fs/cgroup/memory.current').read_text()))
BASE_RUNNER=ROOT/'scripts/v08-v07-run.py'
BASE_RUNNER_SHA='e10b29f13de34a51a698a13ef56afd70d55eb7e2609751c63e878a9642c08c48'
assert sha(BASE_RUNNER)==BASE_RUNNER_SHA
CAPTURE_LINES=100000
POLICY_FILE=ROOT/'scripts/v08-published-bindings.json'
POLICY_SHA='d83a00d780e5b4626b5200a36ad123993b9bbfbf5507837f6445c7f931526c13'
def verify_peer():
 policy_path=ROOT/'scripts/v08-published-bindings.json'
 assert sha(policy_path)=='d83a00d780e5b4626b5200a36ad123993b9bbfbf5507837f6445c7f931526c13','published binding policy identity'
 policy=json.loads(policy_path.read_text());base=policy['published_head']
 assert base=='24149fd567ec273e5c72760ecf0a25a940c4c4fc'
 subprocess.run(['git','--no-optional-locks','-C',str(ROOT),'merge-base','--is-ancestor',base,'HEAD'],check=True)
 actual={str(p.relative_to(ROOT)) for p in (ROOT/'Solidity/Backend/InternalFlow').glob('*.lean')}
 assert actual=={p for p in policy['published_sources'] if p.startswith('Solidity/Backend/InternalFlow/')},'no parallel P1 relay copies'
 for name,digest in policy['published_sources'].items():
  p=ROOT/name;assert p.is_file() and not p.is_symlink() and sha(p)==digest,'published source '+name
  assert subprocess.check_output(['git','--no-optional-locks','-C',str(ROOT),'show',base+':'+name])==p.read_bytes(),'exact published blob '+name
 assert subprocess.check_output(['git','--no-optional-locks','-C',str(ROOT),'show',base+':lean-toolchain'])==(ROOT/'lean-toolchain').read_bytes()
 assert policy['private_v07_head'] is None and not policy['private_v07_sources'],'all V07 modules must be published'
 expected=set(policy['private_v07_sources'])|{p for p in policy['published_sources'] if p.startswith('Solidity/Lowering/V07/')}
 assert {str(p.relative_to(ROOT)) for p in (ROOT/'Solidity/Lowering/V07').glob('*.lean')}==expected
 for name,digest in policy['private_v07_sources'].items():
  p=ROOT/name;assert p.is_file() and not p.is_symlink() and not p.stat().st_mode & 0o222 and sha(p)==digest,'private unpublished source '+name
  assert subprocess.check_output(['git','--no-optional-locks','-C',str(ROOT),'show',policy['private_v07_head']+':'+name])==p.read_bytes()
 return policy

def sources(root=ROOT):
 if root==ROOT:verify_peer()
 return {str(p.relative_to(root)):sha(p) for p in root.rglob('*') if p.is_file() and '.lake' not in p.parts and (p.suffix=='.lean' or p.name in ['lean-toolchain','lakefile.toml','lake-manifest.json'])}
def secret_free(text):
 assert not re.search(r'-----BEGIN [A-Z ]*PRIVATE KEY|https?://[^/\s:@]+:[^/\s@]+@|(?:PASSWORD|SECRET|API_KEY|ACCESS_TOKEN)=[^\s\x00"\']+',text,re.I),'possible credential; retain privately, do not export'
def demux(raw):
 out=[];i=0
 while i<len(raw):
  assert i+8<=len(raw) and raw[i] in [1,2] and raw[i+1:i+4]==b'\0\0\0','invalid log header'
  n=int.from_bytes(raw[i+4:i+8],'big');assert i+8+n<=len(raw),'truncated log frame';out.append(raw[i+8:i+8+n]);i+=8+n
 assert i==len(raw);return b''.join(out)
def belongs_to(cgroup,cid):
 return any(part in [cid,'docker-'+cid+'.scope'] for line in cgroup.splitlines()
  for part in line.split(':',2)[-1].split('/'))
def serial_sample(cid):
 j=get('/containers/'+cid+'/top?ps_args=-eo%20pid,comm,rss');rows=j['Processes']
 if rows is None:
  # Docker may finish between the loop's running check and top. A null
  # process list is accepted ONLY after proving this exact container stopped.
  stopped=get('/containers/'+cid+'/json')
  assert not stopped['State']['Running'] and stopped['State']['Pid']==0, 'null top for live/uncertain container'
  rows=[]
 rss=sum(int(row[2])*1024 for row in rows)
 own_lean=[];own_lake=[]
 # Process turnover between Docker top and /proc is normal. Prove actual
 # cgroup ownership, not membership in a stale PID snapshot (H1 probe evidence).
 for p in pathlib.Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   comm=(p/'comm').read_text().strip()
   if comm not in ['lean','lake']:continue
   cg=(p/'cgroup').read_text()
  except FileNotFoundError:continue
  assert belongs_to(cg,cid), 'outside Lean/Lake cgroup pid='+p.name+' comm='+comm+' cgroup='+cg.strip()
  (own_lean if comm=='lean' else own_lake).append(int(p.name))
 assert len(own_lean)<=1,'competing Lean processes';assert rss<=LIMIT
 return {'aggregate_rss':rss,'lean_processes':len(own_lean),'own_lean_pids':own_lean,'own_lake_pids':own_lake}
def verify(j,profile,image):
 assert j['Name']=='/'+NAME
 assert not j['HostConfig']['Privileged'] and not j['HostConfig']['PidMode']
 assert not any(j['HostConfig'].get(k) for k in ['CapAdd','Devices','DeviceRequests','SecurityOpt'])
 assert not j['Config']['Tty']
 assert j['Image']==profile['Image'] and j['Config']['Cmd']==profile['Cmd']
 for k in ['User','WorkingDir']:assert j['Config'][k]==profile[k],k
 expected={x.split('=',1)[0]:x for x in image['Config'].get('Env',[])}
 expected.update({x.split('=',1)[0]:x for x in profile['Env']});assert sorted(j['Config']['Env'])==sorted(expected.values())
 labels=dict(image['Config'].get('Labels') or {});labels.update(profile['Labels']);assert j['Config']['Labels']==labels
 for k in ['Memory','MemorySwap','NanoCpus','NetworkMode']:assert j['HostConfig'][k]==profile['HostConfig'][k]
 exp={}
 for b in profile['HostConfig']['Binds']:
  a=b.split(':');exp[a[1]]=(a[0],len(a)==2)
 assert {m['Destination']:(m['Source'],m['RW']) for m in j['Mounts']}==exp and all(m['Type']=='bind' for m in j['Mounts'])
def ensure_stopped(cid,token):
 j=get('/containers/'+cid+'/json',True);assert j['Id']==cid and j['Config']['Labels'].get('org.solidity.v08.integrated.token')==token
 if j['State']['Running']:
  s,_=api('POST','/containers/'+cid+'/kill',cleanup=True);assert s in [204,409]
 stop=time.monotonic()+10
 while True:
  j=get('/containers/'+cid+'/json',True)
  if not j['State']['Running'] and j['State']['Pid']==0:return j
  if time.monotonic()>stop:raise RuntimeError('owned runtime did not stop')
  time.sleep(.1)
def run():
 global DEADLINE,ACTIVE_OUT
 assert os.environ.get('V08_TOOL_LOCK_FD')=='9','shared gate requires inherited writer lease'
 lock=os.fdopen(os.dup(9),'r+')
 expected_lock=pathlib.Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock').stat()
 actual_lock=os.fstat(lock.fileno());assert (actual_lock.st_dev,actual_lock.st_ino)==(expected_lock.st_dev,expected_lock.st_ino),'writer lease identity'
 fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 out=E/('run-'+str(time.time_ns()));out.mkdir();ACTIVE_OUT=out;cid=None;started=False;reason=None;samples=[];actual=None;cleanup_ok=False;source=None;controls=None;prefix=b'';source_checked=False;protected_before=None;old_source=None;old_head=None
 if TOKEN_FILE.exists():token=json.loads(TOKEN_FILE.read_text())['token']
 else:token=uuid.uuid4().hex;put(TOKEN_FILE,{'token':token})
 def interrupted(signum,frame):raise RuntimeError('controller signal '+str(signum))
 for signum in [signal.SIGTERM,signal.SIGINT,signal.SIGALRM]:signal.signal(signum,interrupted)
 try:
  assert free_ram()>=RAM_RESERVE and disk()>=500000000
  assert int(pathlib.Path('/sys/fs/cgroup/memory.max').read_text())==17179869184
  assert len(pathlib.Path('/proc/swaps').read_text().splitlines())==1
  allc=get('/containers/json?all=1');assert all(c['State'] not in ['running','paused','restarting'] for c in allc)
  for p in pathlib.Path('/proc').iterdir():
   if p.name.isdigit():
    try:assert (p/'comm').read_text().strip() not in ['lean','lake']
    except FileNotFoundError:pass
  cfg=E/'runtime-integrated.toml'
  settings=tomllib.loads(cfg.read_text());assert all('-j1' in x.get('weakLeanArgs',[]) for x in settings['lean_lib']+settings['lean_exe'])
  spec=importlib.util.spec_from_file_location('graph',ROOT/'scripts/v08-build-graph.py');g=importlib.util.module_from_spec(spec);sys.dont_write_bytecode=True;spec.loader.exec_module(g)
  assert sys.argv[1:]==[]
  requested=['Solidity.KeySort']
  assert (E/'focused-modules.txt').read_text().splitlines()==g.SourceGraph(ROOT).closure(requested)+['@shared-file']
  put(out/'requested-targets.json',{'requested':requested,'mode':'shared-gate-per-file-under-original-caps','Decision_omitted_from_full_gate':False,'meaning':'Separate component gate, never a default/full replacement'})
  old=get('/containers/47c5808627ffeadf7d11884f8c37dd554eae2ed7bc5d55756781500b6ecf9a20/json');image=get('/images/'+old['Image']+'/json');secret_free(json.dumps(image['Config']))
  binds=[m['Source']+':'+m['Destination']+('' if m['RW'] else ':ro') for m in old['Mounts'] if m['Destination']!='/workspace/v08-world-lowering-public099']+[str(ROOT)+':'+str(ROOT),str(E)+':'+str(E)]
  for b in binds:assert pathlib.Path(b.split(':')[0]).exists()
  profile={'Image':old['Image'],'User':str(os.getuid())+':'+str(os.getgid()),'WorkingDir':str(ROOT),'Env':['LEAN_NUM_THREADS=1','LAKE_CACHE_DIR=','LAKE_ARTIFACT_CACHE=false'],'Cmd':['timeout','--signal=KILL','600','sh',str(ROOT/'scripts/v08-integrated-check.sh')],'HostConfig':{'Memory':LIMIT,'MemorySwap':LIMIT,'NanoCpus':1000000000,'NetworkMode':'none','Binds':binds},'Labels':{'org.solidity.v08.integrated.token':token}}
  put(out/'create-or-reuse-intent.json',profile)
  s,b=api('GET','/containers/'+NAME+'/json');assert s==200,'Existing runtime required; no allocation'
  if s==200:cid=json.loads(b)['Id']
  else:
   assert s==404
   try:s,b=api('POST','/containers/create?name='+NAME,profile);assert s==201,(s,b[:100]);cid=json.loads(b)['Id']
   except BaseException:
    s,b=api('GET','/containers/'+NAME+'/json',cleanup=True)
    if s==200:cid=json.loads(b)['Id']
    raise
  j=get('/containers/'+cid+'/json');verify(j,profile,image);assert not j['State']['Running'] and j['State']['Pid']==0
  put(out/'runtime.json',{'id':cid,'token':token,'profile':profile})
  protected_ids=[c['Id'] for c in allc if c['Id']!=cid]
  def protected():
   records={}
   for ident in protected_ids:
    value=get('/containers/'+ident+'/json',True);value['Mounts']=sorted(value['Mounts'],key=lambda m:m['Destination']);records[ident]=hashlib.sha256(json.dumps(value,sort_keys=True).encode()).hexdigest()
   return records
  protected_before=protected();oldroot=pathlib.Path('/workspace/v08-world-lowering-public099');old_source=sources(oldroot);old_head=subprocess.check_output(['git','--no-optional-locks','-C',str(oldroot),'rev-parse','HEAD'],text=True).strip();root_head=subprocess.check_output(['git','--no-optional-locks','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip()
  put(out/'protected-before.json',{'containers':protected_before,'old_source':old_source,'old_head':old_head,'root_head':root_head})
  source=sources();controls={str(p):sha(p) for p in [pathlib.Path(__file__),BASE_RUNNER,ROOT/'scripts/v08-integrated-check.sh',ROOT/'scripts/v08-build-graph.py',POLICY_FILE,ROOT/'scripts/v08-p1-peer-policy.json',ROOT/'scripts/v08-p8a-peer-policy.json',ROOT/'scripts/v08-p1-v2-peer-policy.json',E/'focused-modules.txt',cfg,E/'coord-access/tools/try-tactics.sh',E/'coord-access/tools/gate.sh',E/'coord-access/bin/lake',E/'coord-access/installed.goal',E/'coord-access/current-file.txt',ROOT/'scripts/v08-coord-file.py',E/'coord-access/host-bin/lake',pathlib.Path('/workspace/coord-tools/gate.sh')]}
  previous_finished=j['State']['FinishedAt'];prefix=b''
  (out/'prefix.raw').write_bytes(prefix)
  (out/'target-list.txt').write_bytes((E/'focused-modules.txt').read_bytes())
  put(out/'before.json',{'peer':verify_peer(),'source':source,'controls':controls,'profile':profile,'free_ram':free_ram(),'disk':disk(),'prefix_bytes':len(prefix),'prefix_sha256':hashlib.sha256(prefix).hexdigest(),'log_mode':'invocation-start-window-v2','previous_finished_at':previous_finished})
  print('RUN',out,flush=True);DEADLINE=time.monotonic()+WALL;signal.alarm(WALL);started=True
  s,b=api('POST','/containers/'+cid+'/start');assert s==204,(s,b[:100])
  current=get('/containers/'+cid+'/json');invocation_start=current['State']['StartedAt'];assert invocation_start>previous_finished
  put(out/'invocation-window.json',{'container':cid,'started_at':invocation_start,'since':log_since(invocation_start),'previous_finished_at':previous_finished,'scope':'ALL console emitted after this actual container start; prior cumulative logs retained untouched'})
  with open(out/'samples.jsonl','w') as f:
   while True:
    j=get('/containers/'+cid+'/json')
    if not j['State']['Running']:break
    sample=serial_sample(cid);sample.update({'elapsed':WALL-(DEADLINE-time.monotonic()),'free_ram':free_ram(),'disk':disk()});samples.append(sample);f.write(json.dumps(sample)+'\n');f.flush()
    assert sample['free_ram']>=RAM_RESERVE,'H1 4GiB RAM reserve'
    assert sample['disk']>=300000000,'H1 300MB disk headroom'
    time.sleep(min(1,max(.01,DEADLINE-time.monotonic())))
 except BaseException as ex:reason=type(ex).__name__+': '+str(ex)
 finally:
  signal.alarm(0);DEADLINE=None
  for sig in [signal.SIGTERM,signal.SIGINT]:signal.signal(sig,signal.SIG_IGN)
  if cid:
   try:j=ensure_stopped(cid,token);actual=j['State']['ExitCode'];cleanup_ok=True
   except BaseException as ex:reason=(reason or '')+'; cleanup '+str(ex)
  try:
   if started:
    assert j['State']['StartedAt']==invocation_start
    query='/containers/'+cid+'/logs?stdout=1&stderr=1&since='+log_since(invocation_start)+'&tail='+str(CAPTURE_LINES)
    s,cumulative=api('GET',query,cleanup=True);assert s==200
    assert prefix==b''
    raw=cumulative[len(prefix):];decoded=demux(raw);secret_free(decoded.decode(errors='replace'));(out/'raw.log').write_bytes(raw);(out/'build.log').write_bytes(decoded)
    lines=decoded.decode(errors='replace').splitlines()
    expected_prefix=['Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)','Lake version 5.0.0-src+797c613 (Lean version 4.24.0)']
    assert lines[:2]==expected_prefix and len(lines)<CAPTURE_LINES,'bounded suffix omitted invocation start'
    assert re.findall(r'^H1_CGROUP_PEAK=(\d+)$',decoded.decode(errors='replace'),re.M),'bounded suffix missing invocation end'
    put(out/'capture-policy.json',{'mode':'complete-since-window-bounded-suffix','line_bound':CAPTURE_LINES,'decoded_lines':len(lines),'exact_start_prefix':True,'end_peak_present':True,'actual_query':query,'base_runner_sha256':BASE_RUNNER_SHA,'API_timeout_unchanged':5,'wall_unchanged':WALL,'response_bound_unchanged':32*1024**2})
    put(out/'runtime-after.json',j)
    put(out/'log-bindings.json',{'raw_sha256':sha(out/'raw.log'),'decoded_sha256':sha(out/'build.log'),'cumulative_sha256':hashlib.sha256(cumulative).hexdigest(),'prefix_sha256':hashlib.sha256(prefix).hexdigest(),'scope':'invocation-start-window-v2','query':query})
    assert source==sources() and all(sha(pathlib.Path(p))==h for p,h in controls.items()),'source/config inventory changed'
    assert old_source==sources(oldroot) and old_head==subprocess.check_output(['git','--no-optional-locks','-C',str(oldroot),'rev-parse','HEAD'],text=True).strip() and root_head==subprocess.check_output(['git','--no-optional-locks','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip() and protected_before==protected(),'protected prior source/container changed'
    source_checked=True
    assert samples and max(s['aggregate_rss'] for s in samples)>0,'zero resource samples/RSS'
    assert not j['State']['OOMKilled'],'OOMKilled'
    text=decoded.decode(errors='replace');lines=text.splitlines();assert 'Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)' in lines and 'Lake version 5.0.0-src+797c613 (Lean version 4.24.0)' in lines,'exact tool versions missing'
    peaks=re.findall(r'H1_CGROUP_PEAK=(\d+)',text);assert peaks and 0<int(peaks[-1])<=LIMIT,'missing/invalid cgroup peak'
    key=text.split('H1_TARGET=Solidity.KeySort',1)[1].split('H1_TARGET=',1)[0];assert 'Build completed successfully' in key,'KeySort build not passed'
  except BaseException as ex:reason=(reason or '')+'; evidence '+str(ex)
  gate_exit=125 if reason or not cleanup_ok else actual
  result={'exit':gate_exit,'actual_exit':actual,'reason':reason,'container':cid,'cleanup_stopped':cleanup_ok,'samples':len(samples),'peak_aggregate_rss':max((s['aggregate_rss'] for s in samples),default=None),'peak_child_cgroup':int(peaks[-1]) if 'peaks' in locals() and peaks else None,'minimum_free_ram':min((s['free_ram'] for s in samples),default=None),'source_and_controls_checked':source_checked,'H1':True}
  if (out/'build.log').exists():result['log_sha256']=sha(out/'build.log')
  put(out/'result.json',result);print(json.dumps(result),flush=True)
 return result['exit'] if result['exit'] is not None else 125
if __name__=='__main__':sys.exit(run())
