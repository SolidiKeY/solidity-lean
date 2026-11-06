#!/usr/bin/env python3
"""Strict evidence checks for public099 and the ONE reused application runtime.
Historical production checkers/pins remain unchanged. No build, start or write.
"""
import hashlib,json,re,subprocess,sys,http.client,socket
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
PUBLIC='099bfbe185731c354b12a40f28ccf5d98534c779'
FROZEN='fb379ae20f10e2c92113453ddd9d40d8f2efbe09'
OLD='7c3c8274eeafe908a1e96709d0491c02b306e03f'
CID='47c5808627ffeadf7d11884f8c37dd554eae2ed7bc5d55756781500b6ecf9a20'
PROPOSAL=Path('/workspace/v08-world-lowering-artifacts/published-099-runtime-proposal-20261101')
LIMIT=12884901888
H=lambda b:hashlib.sha256(b).hexdigest()
def digest(p):return H(Path(p).read_bytes())
def validate_profile(profile):
 model=json.loads((PROPOSAL/'runtime-proposal.json').read_bytes())
 expected=model['proposed_additional_same_VM_runtime_profile']
 expected['Cmd']=['timeout','--signal=KILL','600',*expected['Cmd']]
 assert profile==expected,'changed runtime profile'
 assert profile['HostConfig']['Memory']==profile['HostConfig']['MemorySwap']==LIMIT
 assert profile['HostConfig']['NanoCpus']==1000000000
 assert profile['HostConfig']['NetworkMode']=='none'
 assert set(profile['Env'])=={'LEAN_NUM_THREADS=1','LAKE_CACHE_DIR=','LAKE_ARTIFACT_CACHE=false'}
 assert profile['WorkingDir']==str(ROOT) and profile['User']=='1000:1000'
 return model
class Docker(http.client.HTTPConnection):
 def connect(self):
  self.sock=socket.socket(socket.AF_UNIX,socket.SOCK_STREAM)
  self.sock.settimeout(self.timeout);self.sock.connect('/var/run/docker.sock')
def docker_get(path):
 c=Docker('localhost',timeout=5);c.request('GET',path)
 r=c.getresponse();assert r.status==200;j=json.loads(r.read());c.close();return j

def validate_image_environment(observed,profile,image,resolved):
 assert observed['Image']==image['Id']==resolved,'changed resolved image'
 expected=dict(x.split('=',1) for x in image.get('Config',{}).get('Env',[]))
 expected.update(dict(x.split('=',1) for x in profile['Env']))
 assert dict(x.split('=',1) for x in observed['Config']['Env'])==expected,'changed complete environment'

def check(path):
 result=json.loads(Path(path).read_bytes())
 assert result['exit']==result['actual_container_exit']==0
 assert result['guard_stop'] is None and result['monitor_error'] is None
 for key in ['cleanup_verified','measurement_and_bindings_valid','source_unchanged','old_containers_unchanged','no_new_goal_or_vm','no_delete','no_duplication']:
  assert result[key] is True,key
 assert result['container_id']==CID and result['candidate_base']==PUBLIC and result['old_head']==OLD
 assert 0<result['wall_seconds']<600 and result['independent_inner_timeout_seconds']==600
 assert result['samples']>0 and 0<result['peak_aggregate_rss']<=LIMIT
 assert 0<result['cgroup_peak']<=LIMIT
 logpath=Path(result['log']);directory=logpath.parent
 assert directory.is_relative_to(Path('/workspace/v08-world-lowering-evidence/public099-application-20261101'))
 assert digest(logpath)==result['log_sha256']
 raw=(directory/'docker-logs.raw').read_bytes();cumulative=(directory/'docker-logs.cumulative.raw').read_bytes()
 assert H(raw)==result['raw_log_sha256'] and H(cumulative)==result['cumulative_raw_log_sha256']
 boundary=json.loads((directory/'log-boundary.json').read_bytes());prefix=Path(boundary['previous_raw']).read_bytes()
 assert H(prefix)==boundary['sha256']==result['log_prefix_sha256'] and len(prefix)==boundary['bytes']
 assert cumulative==prefix+raw
 decoded=[];remaining=raw
 while remaining:
  assert len(remaining)>=8 and remaining[0] in [0,1,2] and remaining[1:4]==b'\0\0\0'
  size=int.from_bytes(remaining[4:8],'big');assert size+8<=len(remaining)
  decoded.append(remaining[8:8+size]);remaining=remaining[8+size:]
 assert b''.join(decoded)==logpath.read_bytes()
 log=logpath.read_text();assert not re.search(r'^error:',log,re.MULTILINE)
 versions=['Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)','Lake version 5.0.0-src+797c613 (Lean version 4.24.0)']
 assert result['tool_versions']==versions
 assert [x for x in log.splitlines() if x.startswith(('Lean (version ','Lake version '))]==versions
 assert 'Build completed successfully (2 jobs).' in log
 assert re.findall(r'^V08_CGROUP_PEAK=(\d+)$',log,re.MULTILINE)==[str(result['cgroup_peak'])]
 operation=json.loads((directory/'operation-started.json').read_bytes());profile=operation['profile'];model=validate_profile(profile)
 assert operation['profile_sha256']==H(json.dumps(profile,sort_keys=True).encode())
 assert operation['controller_sha256']==digest(ROOT/'scripts/v08-public099-run.py')
 assert operation['proposal_sha256']==digest(PROPOSAL/'runtime-proposal.json')
 assert result['config_sha256']==model['source_config']['sha256']==digest(model['source_config']['path'])
 assert result['modules']==model['source_config']['ordered_serial_modules']
 observed=docker_get('/containers/'+CID+'/json');assert observed['Id']==CID and not observed['State']['Running'] and observed['State']['ExitCode']==0
 assert observed['Config']['Labels']['org.solidity.v08.run']==result['token']==operation['token']
 for key in ['Memory','MemorySwap','NanoCpus','NetworkMode']:assert observed['HostConfig'][key]==profile['HostConfig'][key]
 for key in ['Cmd','WorkingDir','User']:assert observed['Config'][key]==profile[key]
 image=docker_get('/images/'+profile['Image']+'/json')
 reused=json.loads((directory/'reused-id.json').read_bytes())
 validate_image_environment(observed,profile,image,reused['image_id'])
 assert operation['name']==result['name']==model['proposed_container_name']==observed['Name'].lstrip('/')
 prepared=json.loads((PROPOSAL/'runtime-proposal.json').read_bytes())['proposed_additional_same_VM_runtime_profile']
 assert operation['prepared_profile_sha256']==H(json.dumps(prepared,sort_keys=True).encode())
 assert not observed['HostConfig']['Privileged'] and not observed['HostConfig']['PidMode']
 expectedmounts={x.split(':')[1]:(x.split(':')[0],not x.endswith(':ro')) for x in profile['HostConfig']['Binds']}
 assert {m['Destination']:(m['Source'],m['RW']) for m in observed['Mounts']}==expectedmounts
 cleanup=json.loads((directory/'cleanup.json').read_bytes());assert cleanup['id']==CID and cleanup['owned_token_verified'] and cleanup['verified_stopped']
 samples=[json.loads(x) for x in (directory/'samples.jsonl').read_text().splitlines()]
 assert len(samples)==result['samples'] and max(x['rss'] for x in samples)==result['peak_aggregate_rss']
 for x in samples:
  assert x['rss']<=LIMIT and x['lean_processes']<=1 and x['available']>=2*1024**3 and x['parent_current']<=14*1024**3 and x['disk_available']>=540000000
 assert max(x['memory_usage'] for x in samples)==result['peak_sampled_cgroup_usage']
 names=set(subprocess.check_output(['git','ls-files','-z','--cached','--others','--exclude-standard','*.lean','lean-toolchain','lakefile.toml'],cwd=ROOT).decode().split('\0'))-{''}
 assert names==set(result['source_sha256']),'source inventory changed'
 for name,sha in result['source_sha256'].items():assert digest(ROOT/name)==sha,('stale source',name)
 for base in [FROZEN,PUBLIC]:subprocess.run(['git','merge-base','--is-ancestor',base,'HEAD'],cwd=ROOT,check=True)
 expected=json.loads((ROOT/'scripts/v08-axiom-pins.json').read_bytes())
 old=json.loads(subprocess.check_output(['git','show',OLD+':scripts/v08-axiom-pins.json'],cwd=ROOT))
 assert len(old)==832 and all(expected.get(k)==v for k,v in old.items()),'old axiom sets changed'
 found={}
 for name,axes in re.findall(r"'(Solidity\.Lowering\.V08\.[^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log):
  actual=sorted(x.strip() for x in axes.split(',') if x.strip());assert set(actual)<={'propext','Classical.choice','Quot.sound'}
  if name in found:assert found[name]==actual
  found[name]=actual
 assert found==expected,('axiom inventory mismatch',set(expected)-set(found),set(found)-set(expected))
 theorems=set()
 for p in (ROOT/'Solidity/Lowering/V08').glob('*.lean'):
  source=p.read_text();namespace=re.search(r'^namespace ([A-Za-z0-9_.]+)',source,re.MULTILINE)
  if namespace:theorems.update(namespace.group(1)+'.'+n for n in re.findall(r'^theorem ([A-Za-z0-9_]+)',source,re.MULTILINE))
 assert theorems==set(expected),('unprinted theorem',theorems^set(expected))
 core = ['SourceTransient', 'SourceAbi', 'SourceCustomErrorFailures', 'SourceCustomErrors', 'SourceDispatch', 'SourceCallable', 'SourceEmit', 'SourceKeccak', 'SourceFailures', 'SourceEnvironment', 'Callable', 'AbiObservations', 'Transactions', 'TransactionPrefixes', 'LibraryCreation', 'CallableMetadata', 'EnvironmentProjection', 'SelectorObservations', 'CryptoObservations', 'PayableMetadata', 'DeclarationRoles', 'InheritedMetadata']
 seen = set()
 def visit(module):
  if module in seen: return
  seen.add(module)
  # Match the repository's source-elaborator boundary. AST's existing import
  # of built-in Lean is preserved; no external package dependency is introduced.
  forbidden = re.match(r'^Solidity\.(?:Tools\.SolCases$|Syntax\.(?:Elab|Quote|Splice)(?:\.|$)|Calculus\.(?:Print[^.]*|Surface[^.]*|TacticSyntax|Quote|NamedTerm)(?:\.|$)|Frontend\.)', module)
  assert not forbidden, ('owned core reaches source elaborator', module)
  path = ROOT / (module.replace('.', '/') + '.lean')
  if path.exists():
   for line in path.read_text().splitlines():
    if line.startswith('import '):
     for dependency in line[7:].split():
      if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', dependency): visit(dependency)
 for module in core:
  requested='Solidity.Lowering.V08.'+module
  assert (ROOT/(requested.replace('.','/')+'.lean')).is_file(),('missing core root',requested)
  visit(requested)
 requested='Solidity.Semantics.AbiEntryProofs'
 assert (ROOT/(requested.replace('.','/')+'.lean')).is_file()
 visit(requested)
 for name in ['Solidity.lean','docs/module-map.md','docs/README.md']:
  incoming=subprocess.check_output(['git','show',PUBLIC+':'+name],cwd=ROOT)
  assert (ROOT/name).read_bytes().startswith(incoming),('not append-only',name)
 paths=set(subprocess.check_output(['git','diff','--name-only',PUBLIC],cwd=ROOT,text=True).splitlines())
 paths.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=ROOT,text=True).splitlines())
 for p in paths:assert p.startswith(('Solidity/Lowering/V08/','scripts/v08-')) or p in ['Solidity.lean','docs/module-map.md','docs/README.md','docs/feature-work/roadmap-v08-world-lowering.md'],('ownership',p)
 doc=ROOT/'docs/feature-work/roadmap-v08-world-lowering.md'
 for link in re.findall(r'\]\(([^)#]+)(?:#[^)]*)?\)',doc.read_text()):
  if not link.startswith(('http:','https:')):assert (doc.parent/link).exists(),('owned link',link)
 print('PASS:',len(expected),'exact standard axiom sets; all832prior sets unchanged; exact source/config/log-prefix/runtime/guards; public099 ownership; no full-gate claim')
if __name__=='__main__':check(sys.argv[1])
