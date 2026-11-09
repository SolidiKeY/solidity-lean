#!/usr/bin/env python3
"""Kernel controller/ancestor and mounted writer-lock controls; no Lean run."""
import argparse,fcntl,json,os,tempfile
from pathlib import Path
from bounded import cap_kind,controller_mount,settings
ap=argparse.ArgumentParser(); ap.add_argument('--out',type=Path,required=True); a=ap.parse_args()
lock=open('/h78-writer.lock','r'); fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert cap_kind()=='cgroup'; effective=settings(); parent=os.environ['H78_VM_CGROUP']
mounts=[controller_mount('/sys/fs/cgroup'),controller_mount(parent)]
with tempfile.TemporaryDirectory() as temp:
    fake=Path(temp); (fake/'memory.max').write_text(str(16*1024**3)); (fake/'memory.current').write_text('0')
    os.environ['H78_VM_CGROUP']=temp
    try:
        cap_kind()
    except RuntimeError as error:
        assert str(error)=='H78_CONTROLLER_MOUNT_UNVERIFIED'
    else: raise AssertionError('regular-directory controller accepted')
    finally: os.environ['H78_VM_CGROUP']=parent
identity=os.environ['H78_CONTROLLER_ID_FILE']; cid=json.loads(Path(identity).read_text())['container_id']
job=Path('/sys/fs/cgroup').stat(); under=(Path(parent)/'docker'/cid).stat()
assert (job.st_dev,job.st_ino)==(under.st_dev,under.st_ino)
with tempfile.TemporaryDirectory() as temp:
    wrong=Path(temp)/'identity.json'; wrong.write_text(json.dumps({'container_id':'0'*64}))
    os.environ['H78_CONTROLLER_ID_FILE']=str(wrong)
    try:
        cap_kind()
    except RuntimeError as error:
        assert str(error)=='H78_VM_CONTROLLER_NOT_ANCESTOR'
    else: raise AssertionError('wrong controller identity accepted')
    finally: os.environ['H78_CONTROLLER_ID_FILE']=identity
a.out.mkdir(parents=True,exist_ok=False)
(a.out/'result.json').write_text(json.dumps({'status':'pass','settings':effective,'controller_mounts':mounts,'regular_directory_controller_rejected':True,'wrong_job_identity_rejected':True,'verified_controller_node':{'device':job.st_dev,'inode':job.st_ino,'relative_to_vm':'docker/'+cid},'writer_lock':'exclusive lock on host bind-mounted writer.lock held by this process','boundary':'Controller/lock validation only; no Lean or proof gate'},indent=2)+'\n')
print('PASS: actual8GiB/swap0, ancestor controller, fake directory rejected, host writer lock held')
