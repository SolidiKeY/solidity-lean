#!/usr/bin/env python3
"""Local hard-cap executor. Evidence stays outside git; no Lean server.
The runner verifies one active Lean process and explicit -j1. A non-Lean heavy
command is outside this runner's accepted use. Every failure is retained.
"""
import argparse, fcntl, hashlib, json, os, pathlib, re, signal, subprocess, time, uuid
p=argparse.ArgumentParser();p.add_argument('--wall-seconds',type=float,default=600)
p.add_argument('label');p.add_argument('command',nargs=argparse.REMAINDER);a=p.parse_args()
assert re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*',a.label),'simple evidence label required'
assert a.command and 0<a.wall_seconds<=600,'command required; wall budget at most 600s'
root=pathlib.Path(__file__).resolve().parents[3]
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a+')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
out=pathlib.Path('/workspace/source-relations-evidence')/a.label
out.mkdir(parents=True,exist_ok=False)
env=dict(os.environ)
for k in ['DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH']:env.pop(k,None)
docker=['docker','--host=unix:///var/run/docker.sock']
name='h55-source-relations-'+uuid.uuid4().hex
image='ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852'
start=time.monotonic();failures=[];samples=[];cid=None;proc=None;actual=None

def save(name,obj): (out/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def api(args):
    r=subprocess.run(docker+args,env=env,capture_output=True,text=True,timeout=10)
    if r.returncode: raise RuntimeError('Docker '+args[0]+' failed: '+r.stderr[:1000])
    return r.stdout

def free():
    mem=next(int(x.split()[1])*1024 for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
    cg=pathlib.Path('/sys/fs/cgroup')
    return min(mem,int((cg/'memory.max').read_text())-int((cg/'memory.current').read_text()))

def inputs():
    files=subprocess.check_output(['git','ls-files','-z','--cached','--others','--exclude-standard'],cwd=root).decode().split('\0')
    selected=[s for s in files if s and (s.endswith('.lean') or s in ['lakefile.toml','lake-manifest.json','lean-toolchain'] or s.startswith(('scripts/h55/source-relations/','tests/h55/source-relations/','docs/feature-work/h55-source-relations.md')))]
    return {s:hashlib.sha256((root/s).read_bytes()).hexdigest() for s in sorted(set(selected)) if (root/s).is_file() and '__pycache__' not in pathlib.Path(s).parts}

def processes():
    active=[]
    for path in pathlib.Path('/proc').iterdir():
        if not path.name.isdigit():continue
        try:
            comm=(path/'comm').read_text().strip()
            if comm not in ['lean','lake']:continue
            cg=(path/'cgroup').read_text()
            argv=(path/'cmdline').read_bytes().split(b'\0')
            state=(path/'stat').read_text().rsplit(') ',1)[1].split()[0]
            if state=='Z':continue
        except (FileNotFoundError,ProcessLookupError):continue
        assert cid in cg,'competing Lean/Lake process; stop only owned runtime'
        if comm=='lean':
            assert b'-j1' in argv,'Lean invocation missing explicit -j1: pid='+path.name+' argv='+repr(argv)
            active.append(int(path.name))
    assert len(active)<=1,'multiple heavy Lean jobs'
    return active

before=inputs();save('sources.before.json',before)
external={str(pathlib.Path(s)):hashlib.sha256(pathlib.Path(s).read_bytes()).hexdigest() for s in a.command if s.startswith('/workspace/') and pathlib.Path(s).is_file()}
save('external-inputs.before.json',external)
def interrupted(signum,frame):raise RuntimeError('controller signal '+str(signum))
for sig in [signal.SIGTERM,signal.SIGINT]:signal.signal(sig,interrupted)
try:
    assert free()>=4*1024**3,'4 GiB reserve unavailable'
    create=['create','--name',name,'--memory=12g','--memory-swap=12g','--cpus=1','--network=none','--pids-limit=256','-v','/workspace:/workspace','-w',str(root),'-e','LEAN_NUM_THREADS=1','-e','XDG_CACHE_HOME=/workspace/.setup/cache','-e','PATH=/workspace/.setup/tools/lean-4.24.0-linux/bin:/usr/bin:/bin',image]+a.command
    save('command.json',docker+create)
    cid=api(create).strip()
    j=json.loads(api(['inspect',cid]))[0]
    bounds={k:j['HostConfig'][k] for k in ['Memory','MemorySwap','NanoCpus','NetworkMode','PidsLimit']}
    assert bounds=={'Memory':12*1024**3,'MemorySwap':12*1024**3,'NanoCpus':10**9,'NetworkMode':'none','PidsLimit':256},'runtime bounds mismatch'
    assert 'LEAN_NUM_THREADS=1' in j['Config']['Env']
    save('runtime.json',{'Id':j['Id'],'Image':j['Image'],'bounds':bounds,'command':j['Config']['Cmd']})
    with (out/'output.log').open('w') as log:
        proc=subprocess.Popen(docker+['start','--attach',cid],env=env,stdout=log,stderr=subprocess.STDOUT)
        while proc.poll() is None:
            available=free();active=processes()
            samples.append({'available':available,'lean_pids':active,'elapsed':time.monotonic()-start})
            assert available>=4*1024**3,'4 GiB reserve violated'
            assert time.monotonic()-start<a.wall_seconds,'wall budget exhausted'
            time.sleep(.25)
        actual=proc.wait(timeout=10)
    state=json.loads(api(['inspect',cid]))[0]['State'];save('state.json',state)
    assert not state['Running'] and not state['OOMKilled'],'runtime running or OOM killed'
    assert state['ExitCode']==actual==0,'command failed'
except BaseException as error:
    failures.append(str(error))
finally:
    if cid:
        try: api(['rm','--force',cid])
        except BaseException as error: failures.append('cleanup: '+str(error))
    else:
        try:
            state=subprocess.run(docker+['inspect',name],env=env,capture_output=True,text=True,timeout=10)
            if state.returncode==0:api(['rm','--force',name])
        except BaseException as error:failures.append('create-timeout cleanup: '+str(error))
    if proc:
        try: proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill();proc.wait(timeout=10);failures.append('Docker attach timeout')
    after=inputs();save('sources.after.json',after)
    if before!=after:failures.append('source identity changed during check')
    external_after={s:hashlib.sha256(pathlib.Path(s).read_bytes()).hexdigest() for s in external if pathlib.Path(s).is_file()}
    save('external-inputs.after.json',external_after)
    if external!=external_after:failures.append('external command input identity changed')
    save('samples.json',samples)
record={'command':a.command,'actual_exit':actual,'exit':0 if not failures else 125,'failures':failures,'wall_seconds':time.monotonic()-start,'minimum_available':min((s['available'] for s in samples),default=free()),'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()}
save('result.json',record);print(json.dumps(record));raise SystemExit(record['exit'])
