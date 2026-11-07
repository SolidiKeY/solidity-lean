#!/usr/bin/env python3
"""Launch the pinned8GiB controller diagnostic; container acquires the host writer lock."""
import argparse,fcntl,json,os,subprocess,uuid
from pathlib import Path
ap=argparse.ArgumentParser(); ap.add_argument('--out',type=Path,required=True); ap.add_argument('--control-only',action='store_true'); a=ap.parse_args()
root=Path('/workspace/solidity-lean'); evidence=Path('/workspace/h62-migrate-semantics-evidence'); source=Path('/workspace/h62-migrate-semantics-base-8g')
image='python@sha256:4840d514c583a4d3d8cad3940e68dee6f0f6f3635c12fcd0a3d74c21a5b93a54'
env=dict(os.environ)
for key in ['DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH']: env.pop(key,None)
docker=['docker','--host=unix:///var/run/docker.sock']; out=a.out.resolve(); name='h78-semantics-'+uuid.uuid4().hex[:12]
lockfile=Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
mounts=[(root/'scripts/h62/item6/migrate-semantics',root/'scripts/h62/item6/migrate-semantics',True),(source,source,True),(Path('/workspace/.setup/tools/lean-4.24.0-linux'),Path('/workspace/.setup/tools/lean-4.24.0-linux'),True),(evidence/'old-clean-h78-01',evidence/'old-clean-h78-01',True),(Path('/sys/fs/cgroup'),Path('/vm-cgroup'),True),(lockfile,Path('/h78-writer.lock'),True),(out,out,False)]
with lockfile.open('r') as preparation_lock:
    fcntl.flock(preparation_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()!='c6f550e281a7e5affa9a99bc2cdaed556dec00e4': raise SystemExit('BASE_MISMATCH')
    if subprocess.check_output(['git','status','--porcelain','--','Solidity'],cwd=source,text=True): raise SystemExit('BASE_DIRTY')
    out.mkdir(parents=True,exist_ok=False)
    command=docker+['create','--pull=never','--name',name,'--network','none','--read-only','--tmpfs','/tmp:rw,nosuid,nodev','--cap-drop=ALL','--security-opt=no-new-privileges','--memory=8g','--memory-swap=8g','--user=1000:1000']
    for src,dst,readonly in mounts: command+=['--mount','type=bind,src='+str(src)+',dst='+str(dst)+(',readonly' if readonly else '')]
    command+=['--workdir',str(source)]
    for key,value in {'PYTHONDONTWRITEBYTECODE':'1','LEAN_NUM_THREADS':'1','H78_CAP_KIND':'cgroup','H78_VM_CGROUP':'/vm-cgroup','H78_CONTROLLER_ID_FILE':str(out/'container-identity.json'),'H78_RUNTIME_IMAGE':image}.items(): command+=['--env',key+'='+value]
    script='cgroup_controls.py' if a.control_only else 'cgroup_prerequisite.py'
    command+=[image,'python','-u',str(root/'scripts/h62/item6/migrate-semantics'/script),'--out',str(out/'run')]
    created=subprocess.run(command,env=env,capture_output=True,text=True)
    (out/'create.log').write_text(created.stdout+created.stderr)
    if created.returncode: raise SystemExit(created.returncode)
    cid=created.stdout.strip()
    (out/'container-identity.json').write_text(json.dumps({'container_id':cid})+'\n')
# The container acquires the same physical host writer.lock before any Lean
# check; preparation releases it here so the container can acquire it itself.
try:
    fmt='{"image":{{json .Config.Image}},"image_id":{{json .Image}},"memory":{{json .HostConfig.Memory}},"memory_swap":{{json .HostConfig.MemorySwap}},"network":{{json .HostConfig.NetworkMode}},"readonly_root":{{json .HostConfig.ReadonlyRootfs}},"mounts":{{json .Mounts}}}'
    inspected=json.loads(subprocess.check_output(docker+['inspect','--format',fmt,cid],env=env,text=True))
    if inspected['image']!=image or inspected['memory']!=8*1024**3 or inspected['memory_swap']!=8*1024**3: raise RuntimeError('DOCKER_LIMIT_MISMATCH')
    (out/'launch.json').write_text(json.dumps({'create_command':command,'container_id':cid,'inspection':inspected,'writer_lock':'host lock bind-mounted read-only; acquired by container script'},indent=2)+'\n')
    completed=subprocess.run(docker+['start','--attach',cid],env=env,capture_output=True,text=True)
    (out/'container.log').write_text(completed.stdout+completed.stderr)
    (out/'container-state.json').write_text(subprocess.check_output(docker+['inspect','--format','{{json .State}}',cid],env=env,text=True))
    print(completed.stdout+completed.stderr,end=''); code=completed.returncode
finally:
    removed=subprocess.run(docker+['rm','--force',cid],env=env,capture_output=True,text=True)
    (out/'cleanup.log').write_text(removed.stdout+removed.stderr)
raise SystemExit(code)
