#!/usr/bin/env python3
"""Validate H1 component evidence; does not certify default/full/Decision gates."""
import hashlib,json,pathlib,re,sys

PIN_SHA256={'v08-axiom-pins.json': 'bbf9497b64531610b2d778c27d288559d32198a9c49e84e4847513166670fb49', 'v08-h1-axiom-pins.json': '0fe89d90dc084da716ede6114c281cda79ea8a708446630f44477885881b930a', 'v08-prefixed-rethrow-axiom-pins.json': '26194dfe21dc1be940738c4ea939d2fff968f4e1bc627a0f08416fed880397c2', 'v08-rethrow-axiom-pins.json': '97bf4efb235d56181a79a684e31deb81ed7352f84c3d917a627376ce2e3d7954', 'v08-standard-rethrow-axiom-pins.json': '33f19ede9d742e6447d10e0bb763491173b16d03d9acbd51349d909948422966', 'v08-transient-bytes-emit-axiom-pins.json': 'ee54d6deef3875e4946f26e1feec5139a67c802c63db3abf09a4379070e41516', 'v08-transient-emit-axiom-pins.json': 'e1b160d2579533adc66a463de9d52e5ea3fba9afcabdb7bd9548458c9f016a22', 'v08-transient-emit-panic-axiom-pins.json': '7272b5aee0f185561b6773fe6cf74c4a675cdd2b0bb828e0fe82309915945209', 'v08-transient-mixed-axiom-pins.json': 'a8d5d93c2c5d67fc042c7d9a93344e2885c9341831ed22e236c8447b270a6e37', 'v08-transient-rethrow-axiom-pins.json': 'ee6041d02cfa1ed58b3c31242c205922abb2c81b7139e81268ada539876539e5'}

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def validate(root,run):
 result=json.loads((run/'result.json').read_text());before=json.loads((run/'before.json').read_text())
 assert result['exit']==result['actual_exit']==0 and result['reason'] is None
 assert result['cleanup_stopped'] and result['source_and_controls_checked'] and result['samples']>0
 assert result['minimum_free_ram']>=4294967296
 assert 0<result['peak_aggregate_rss']<=12884901888 and 0<result['peak_child_cgroup']<=12884901888
 current={str(p.relative_to(root)):sha(p) for p in root.rglob('*') if p.is_file() and '.lake' not in p.parts and (p.suffix=='.lean' or p.name in ['lean-toolchain','lakefile.toml','lake-manifest.json'])}
 assert current==before['source'],'exact source inventory'
 required={str(root/'scripts'/n) for n in ['v08-h1-validate.py','v08-h1-check.sh','v08-build-graph.py']}|{'/workspace/v08-world-lowering-evidence/h1-recovery-20261102/focused-modules.txt','/workspace/v08-world-lowering-evidence/published-099-investigation-20261101/runtime-public099.toml'}
 assert before['controls'].keys()==required
 for name,digest in before['controls'].items():assert sha(pathlib.Path(name))==digest,('control',name)
 profile=before['profile'];host=profile['HostConfig']
 assert host['Binds']==['/workspace/.setup/tools/lean-4.24.0-linux:/opt/lean:ro', '/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/opt/node:ro', '/workspace/.setup/solkey:/workspace/.setup/solkey:ro', '/workspace/v08-world-lowering-evidence/published-099-investigation-20261101:/workspace/v08-world-lowering-evidence/published-099-investigation-20261101:ro', '/workspace/v08-world-lowering-public099:/workspace/v08-world-lowering-public099', '/workspace/v08-world-lowering-evidence/h1-recovery-20261102:/workspace/v08-world-lowering-evidence/h1-recovery-20261102']
 assert host['Memory']==host['MemorySwap']==12884901888 and host['NanoCpus']==1000000000 and host['NetworkMode']=='none'
 assert profile['Env']==['LEAN_NUM_THREADS=1','LAKE_CACHE_DIR=','LAKE_ARTIFACT_CACHE=false']
 assert profile['Cmd']==['timeout','--signal=KILL','600','sh',str(root/'scripts/v08-h1-check.sh')]
 runtime=json.loads((run/'runtime.json').read_text());actual=json.loads((run/'runtime-after.json').read_text())
 assert runtime['profile']==profile and runtime['id']==actual['Id']==result['container']
 assert not actual['State']['Running'] and actual['State']['Pid']==0 and not actual['State']['OOMKilled'] and actual['State']['ExitCode']==0
 assert actual['Image']==profile['Image']=='sha256:d9b8c34d61a9b9a3c44cab883d7d2f2619d674966ab520186f799cf32e3e0377'
 for k in ['Memory','MemorySwap','NanoCpus','NetworkMode']:assert actual['HostConfig'][k]==host[k]
 assert not actual['HostConfig']['Privileged'] and not actual['HostConfig']['PidMode']
 assert not any(actual['HostConfig'].get(k) for k in ['CapAdd','Devices','DeviceRequests','SecurityOpt'])
 assert actual['Config']['Cmd']==profile['Cmd'] and not actual['Config']['Tty']
 assert profile['WorkingDir']==str(root)==actual['Config']['WorkingDir']
 assert profile['User']==actual['Config']['User']=='1000:1000'
 assert actual['Name']=='/v08-h1-validation-20261102'
 assert profile['Labels']=={'org.solidity.v08.h1.token':runtime['token']}
 assert actual['Config']['Labels']==dict({'org.opencontainers.image.version': '24.04'},**profile['Labels'])
 assert actual['Config']['Labels']['org.solidity.v08.h1.token']==runtime['token']
 assert sorted(actual['Config']['Env'])==sorted(['LEAN_NUM_THREADS=1', 'LAKE_CACHE_DIR=', 'LAKE_ARTIFACT_CACHE=false', 'PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin'])
 expected={}
 for b in host['Binds']:
  a=b.split(':');expected[a[1]]=(a[0],len(a)==2)
 assert all(m['Type']=='bind' for m in actual['Mounts'])
 assert {m['Destination']:(m['Source'],m['RW']) for m in actual['Mounts']}==expected
 assert before['free_ram']>=4294967296 and before['disk']>=500000000
 samples=[json.loads(x) for x in (run/'samples.jsonl').read_text().splitlines()]
 assert len(samples)==result['samples']
 assert result['peak_aggregate_rss']==max(s['aggregate_rss'] for s in samples)
 assert result['minimum_free_ram']==min(s['free_ram'] for s in samples)
 assert all(0<=s['elapsed']<=600 for s in samples)
 assert [s['elapsed'] for s in samples]==sorted(s['elapsed'] for s in samples)
 assert all(s['disk']>=300000000 and s['free_ram']>=4294967296 and s['lean_processes']<=1 and s['aggregate_rss']<=12884901888 for s in samples)
 bindings=json.loads((run/'log-bindings.json').read_text());log=(run/'build.log').read_text()
 assert sha(run/'raw.log')==bindings['raw_sha256']
 assert sha(run/'build.log')==bindings['decoded_sha256']==result['log_sha256']
 raw=(run/'raw.log').read_bytes();decoded=[];i=0
 while i<len(raw):
  assert i+8<=len(raw) and raw[i] in [1,2] and raw[i+1:i+4]==b'\0\0\0'
  n=int.from_bytes(raw[i+4:i+8],'big');assert i+8+n<=len(raw);decoded.append(raw[i+8:i+8+n]);i+=8+n
 assert b''.join(decoded)==(run/'build.log').read_bytes()
 prefix=(run/'prefix.raw').read_bytes()
 assert len(prefix)==before['prefix_bytes']
 assert hashlib.sha256(prefix).hexdigest()==bindings['prefix_sha256']==before['prefix_sha256']
 assert hashlib.sha256(prefix+raw).hexdigest()==bindings['cumulative_sha256']
 assert log.splitlines()[:2]==['Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)','Lake version 5.0.0-src+797c613 (Lean version 4.24.0)']
 assert re.findall(r'^H1_CGROUP_PEAK=(\d+)$',log,re.M)==[str(result['peak_child_cgroup'])]
 assert re.search(r'H1_TARGET=Solidity.KeySort\nBuild completed successfully \(2 jobs\)\.',log)
 assert 'sorryAx' not in log
 targets=(pathlib.Path(next(n for n in before['controls'] if n.endswith('/focused-modules.txt')))).read_text().splitlines()
 assert re.findall(r'^H1_TARGET=(.*)$',log,re.M)==targets
 pins={}
 pinfiles=sorted((root/'scripts').glob('v08*axiom-pins.json'))
 assert {p.name:sha(p) for p in pinfiles}==PIN_SHA256
 for p in pinfiles:
  d=json.loads(p.read_text());assert not pins.keys()&d.keys();pins.update(d)
 found={}
 for name,axioms in re.findall(r"'(Solidity\.Lowering\.V08\.[^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log):
  value=sorted(x.strip() for x in axioms.split(',') if x.strip())
  assert name not in found or found[name]==value;found[name]=value
 assert pins==found and len(pins)==1209
 assert all(set(v)<=set(['propext','Classical.choice','Quot.sound']) for v in pins.values())
 declared=set()
 for p in (root/'Solidity/Lowering/V08').glob('*.lean'):
  text=p.read_text();ns=re.search(r'^namespace (\S+)',text,re.M)
  if ns:declared.update(ns[1]+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M))
 assert declared==pins.keys()
 return {'component':'H1Audit','pins':len(pins),'targets':len(targets),'kernel_component_only':True,'mandatory_full_pass':False}
if __name__=='__main__':
 print(json.dumps(validate(pathlib.Path(sys.argv[1]),pathlib.Path(sys.argv[2])),sort_keys=True))
