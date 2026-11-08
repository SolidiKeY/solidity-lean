# Fixed-budget Linux lane build supervisor. No theorem or proof-result inference.
import sys
sys.path.insert(0,str(__import__('pathlib').Path(__file__).resolve().parent))
from parent_death_guard import prepare_child, owned_shell, result_exit, process, exited_without_reaping, finish_owned, memory_state, resources_allowed, command_line
import pathlib,os,subprocess,time,json,signal,argparse,resource
parser=argparse.ArgumentParser(description='Bounded owned build supervision; fixed original12GiB/no-swap/headroom limits')
parser.add_argument('--profile',choices=['lean','native-editor'],default='lean');parser.add_argument('--output',type=pathlib.Path,required=True);parser.add_argument('--script',type=pathlib.Path,required=True);args=parser.parse_args()
resident_limit=(4 if args.profile=='native-editor' else 12)*1024**3
out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
if any((out/name).exists() for name in ['heavy.log','heavy-resources.jsonl','heavy-result.json','resource-preflight.json']):raise RuntimeError('Preserve prior supervision receipts; choose a new output directory')
repo=pathlib.Path(__file__).resolve().parents[2]
def prepare_bounded_child():
 if args.profile=='lean':resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
 prepare_child()
def proc(pid):
 try:
  x=pathlib.Path('/proc/'+str(pid)+'/stat').read_text();f=x[x.rfind(')')+2:].split();return {'pid':pid,'ppid':int(f[1]),'birth':f[19],'rssBytes':int(f[21])*os.sysconf('SC_PAGE_SIZE'),'vsizeBytes':int(f[20]),'threads':int(f[17]),'name':x[x.find('(')+1:x.rfind(')')],'state':f[0]}
 except (FileNotFoundError,ProcessLookupError):return None
initial=[r for p in pathlib.Path('/proc').iterdir() if p.name.isdigit() and (r:=proc(int(p.name))) and r['name'] in ['lean','lake','dafny','dotnet','code'] and r['state']!='Z']
if initial:raise RuntimeError('Another Lean/Lake process already running; no competing build admitted: '+str(initial))
inherited_as=resource.getrlimit(resource.RLIMIT_AS)
admission={'time':time.time(),**memory_state(),'profile':args.profile,'inheritedAddressSpaceBytes':['unlimited' if x==resource.RLIM_INFINITY else x for x in inherited_as]};admission['allowed']=resources_allowed(admission) and (args.profile!='native-editor' or inherited_as==(resource.RLIM_INFINITY,resource.RLIM_INFINITY))
(out/'resource-preflight.json').write_text(json.dumps(admission,indent=2)+'\n')
if not admission['allowed']:
 result={'command':['bash',str(args.script.resolve())],'exit':None,'supervisorExit':1,'admitted':False,'resourceStop':{'reason':'admission denied',**admission},'ownedSurvivors':[]}
 (out/'heavy-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True);raise SystemExit(1)
log=(out/'heavy.log').open('w');p=subprocess.Popen(['bash','-c',owned_shell(['bash',str(args.script.resolve())])],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=prepare_bounded_child);root_birth=process(p.pid)['birth'];seen={};stop=None;peak=0
with (out/'heavy-resources.jsonl').open('w') as samples:
 samples.write(json.dumps({'phase':'admission','rssBytes':0,'processes':[],**admission})+'\n');samples.flush()
 while not exited_without_reaping(p.pid):
  table={int(d.name):r for d in pathlib.Path('/proc').iterdir() if d.name.isdigit() and (r:=proc(int(d.name)))};ids={p.pid};ids.update(pid for pid,birth in seen.items() if table.get(pid,{}).get('birth')==birth)
  changed=True
  while changed:
   changed=False
   for pid,r in table.items():
    if r['ppid'] in ids and pid not in ids:ids.add(pid);changed=True
  rows=[table[i] for i in ids if i in table];seen.update({r['pid']:r['birth'] for r in rows});rss=sum(r['rssBytes'] for r in rows);peak=max(peak,rss);mem=pathlib.Path('/proc/meminfo').read_text();available=int(next(l for l in mem.splitlines() if l.startswith('MemAvailable:')).split()[1])*1024;swap=int(next(l for l in mem.splitlines() if l.startswith('SwapTotal:')).split()[1])*1024
  for row in rows: row['command'] = command_line(row['pid'], row['birth'])
  samples.write(json.dumps({'time':time.time(),'rssBytes':rss,'availableBytes':available,'swapTotalBytes':swap,'processes':rows})+'\n');samples.flush()
  native_lean=args.profile=='native-editor' and any(r['name'] in ['lean','lake'] for r in rows)
  if native_lean or rss>resident_limit or available<12*1024**3 or swap!=0:
   stop={'reason':'Lean forbidden in native-editor profile' if native_lean else 'resource guard','rssBytes':rss,'availableBytes':available,'swapTotalBytes':swap}
   for r in rows:
    current=proc(r['pid'])
    if current and current['birth']==r['birth']:
     try:os.kill(r['pid'],signal.SIGSTOP)
     except ProcessLookupError:pass
   for r in reversed(rows):
    current=proc(r['pid'])
    if current and current['birth']==r['birth']:
     try:os.kill(r['pid'],signal.SIGKILL)
     except ProcessLookupError:pass
   break
  time.sleep(0.5)
terminal_resources=memory_state()
if stop is None and not resources_allowed(terminal_resources):stop={'reason':'terminal resource guard',**terminal_resources}
retired,survivors=finish_owned(p.pid,root_birth,seen);code=p.wait();log.close();result={'command':['bash',str(args.script.resolve())],'exit':code,'resourceStop':stop,'admitted':True,'admission':admission,'terminalResources':terminal_resources,'peakObservedAggregateRssBytes':peak,'systemdScope':False,'ownedSurvivors':survivors,'retiredAtCompletion':retired,'profile':args.profile,'inheritedAddressSpaceBytes':admission['inheritedAddressSpaceBytes'],'residentLimitBytes':resident_limit,'ulimitVirtualKiB':12582912 if args.profile=='lean' else None,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'authorization':('Lean profile: inherited hardAS12GiB plus aggregateRSS12GiB/no-swap/MemAvailable12GiB guard; no aggregate cgroup' if args.profile=='lean' else 'Native editor profile: supervisor aggregateRSS4GiB plus original native runner4GiB RSS guard/no-swap/MemAvailable12GiB; sampled Lean/Lake detection only; inherited address space unlimited at admission; no aggregate cgroup')};result['supervisorExit']=result_exit(code,stop,retired or survivors);(out/'heavy-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True);raise SystemExit(result_exit(code,stop,retired or survivors))
