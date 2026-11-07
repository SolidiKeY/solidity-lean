"""Bounded stdio MCP supervisor. Caller holds writer.lock during diagnostics.
The lifetime heavy lock excludes builds, including while Lean workers are idle.
"""
import hashlib,json,os,pathlib,signal,subprocess,sys,threading,time,uuid
from resource_guard import available_bytes,heavy_lock
root=pathlib.Path(__file__).resolve().parents[3]
lock=heavy_lock()
if available_bytes()<4*1024**3: raise SystemExit('Insufficient VM/host headroom')
env=os.environ.copy()
for k in ('DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH'): env.pop(k,None)
docker=['docker','--host=unix:///var/run/docker.sock']
cmd=docker+['run','--rm','-i','--name','h28-type-mcp','--network','none','--memory','12g','--memory-swap','12g','--cpus','1','--user','1000:1000',
'--mount','type=bind,src='+str(root)+',dst='+str(root),
'--mount','type=bind,src=/opt/codex/runtimes/codex-primary-runtime/dependencies/python,dst=/opt/codex/runtimes/codex-primary-runtime/dependencies/python,readonly',
'--mount','type=bind,src=/workspace/.setup/tools/lean-4.24.0-linux,dst=/opt/lean,readonly',
'--mount','type=bind,src=/workspace/.setup/cache/lake,dst=/workspace/.setup/cache/lake',
'-w',str(root),'-e','LAKE_CACHE_DIR=/workspace/.setup/cache/lake','-e','LEAN_NUM_THREADS=1','-e','LEAN_LSP_MAX_OPEN_FILES=3','-e','PATH='+str(root)+'/tests/h28-sol/type-grammar/bin:/opt/lean/bin:/usr/bin:/bin',
'ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852','.venv/bin/python','-m','lean_lsp_mcp','--lean-project-path',str(root)]
start=time.monotonic()
inputs=sorted((root/'Solidity/Frontend/TypeGrammarH28').glob('*.lean'))+[pathlib.Path(__file__).resolve(),root/'tests/h28-sol/type-grammar/bin/lake',root/'tests/h28-sol/type-grammar/runtime.toml']
hashes={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
state=dict(command=cmd,source_hashes=hashes,minimum_vm_or_host_headroom_bytes=available_bytes(),guard=None)
proc=subprocess.Popen(cmd,env=env)
finished=threading.Event()
def stop_owned():
    subprocess.run(docker+['stop','-t','1','h28-type-mcp'],env=env,capture_output=True,timeout=3)
def watch():
    while not finished.wait(.5):
        try:
            headroom=available_bytes()
        except Exception as error:
            state['guard']='HEADROOM_UNREADABLE: '+str(error);stop_owned();return
        state['minimum_vm_or_host_headroom_bytes']=min(state['minimum_vm_or_host_headroom_bytes'],headroom)
        if headroom<4*1024**3:
            state['guard']='VM_OR_HOST_HEADROOM';stop_owned();return
thread=threading.Thread(target=watch,daemon=True);thread.start()
def interrupted(signum,frame):
    state['termination_signal']=signum
    finished.set()
    stop_owned()
signal.signal(signal.SIGTERM,interrupted)
signal.signal(signal.SIGINT,interrupted)
try:
    code=proc.wait()
finally:
    finished.set();thread.join(timeout=1)
    state['elapsed_s']=time.monotonic()-start
    state['exit']=proc.poll()
    state['source_unchanged']=all(hashlib.sha256((root/p).read_bytes()).hexdigest()==h for p,h in hashes.items())
    (root/'tests/h28-sol/type-grammar/evidence'/('mcp-resource-'+uuid.uuid4().hex[:12]+'.json')).write_text(json.dumps(state,indent=2)+'\n')
raise SystemExit(1 if state['guard'] else code)
