from pathlib import Path
import os,subprocess,json
root=Path.cwd();new=root/'.lake/native-browser-environment';out=Path('/workspace/scratch/browser-chain/environment')
base=['docker','--host=unix:///var/run/docker.sock','run','--rm','--memory=12g','--memory-swap=12g','--cpus=1','--user=1000:1000','-e','LEAN_NUM_THREADS=1','-e','NATIVE_BROWSER_BOUNDED_GATE=1','-v','/workspace:/workspace','-v','/opt:/opt:ro','-v','/sys/fs/cgroup:/task-outer-cgroup:ro','-w',str(root)]
env={k:v for k,v in os.environ.items() if k not in ['DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH']};common=['python3','tests/directruntime-20261104/native-browser/bounded-command.py'];copies={}
for mode in ['native','direct']:
 target=new/mode;assert not target.exists();target.mkdir();objects=list((root/'.lake/native-browser-address-postmerge'/mode).glob('*.o'))
 for obj in objects:os.link(obj,target/obj.name)
 copies[mode]=len(objects)
(out/'cache-candidates.json').write_text(json.dumps({'copiedContentAddressedObjectCandidates':copies,'boundary':'Candidate keys must pass current builder provenance;candidate reuse is not assumed,no cachedverdict. Freshlinks/manifests required;no matchedcold/performanceacceptance.'},indent=2)+'\n')
for phase,mode,script in [('marker','native',str(new/'marker-gate.sh')),('fixed-byte-marker','native',str(new/'fixed-byte-gate.sh')),('address-marker','native',str(new/'address-marker-gate.sh')),('mcp','native',str(new/'mcp.sh')),('native-build','native','tests/directruntime-20261104/native-browser/hardening-native-build.sh'),('wasm-build','wasm',str(new/'wasm-build.sh'))]:
 args=base.copy()
 if mode=='native':args+=['-v','/usr:/usr:ro','-e',f'NATIVE_BROWSER_NATIVE_OUTPUT={new}/native']
 else:
  args+=['-e','GIT_CONFIG_GLOBAL=/work/native-browser.gitconfig']
  for a,b in [('native-browser-wasm','/work'),('native-browser-prefix','/native:ro'),('native-browser-sdk','/emsdk:ro'),('native-browser-sdk-usr','/usr:ro'),('native-browser-sdk-alternatives','/etc/alternatives:ro')]:args+=['-v',str(root/'.lake'/a)+':'+b]
 args+=['ubuntu:24.04',*common,str(out/(phase+'-gate.json')),'bash',script]
 with (out/(phase+'.log')).open('x') as f:subprocess.run(args,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
