"""Guard H127 package/cache preparation against live or substituted input copies.

Copies an independently SHA-pinned full inventory, never executes inputs, flattens
hard links, and preserves content/mode/owner/mtime/xattrs/internal symlinks.
Requires exclusive writer control. This is preparation, not a sealed mount,
atomic snapshot, whole-stage resource attestation or worker authorization.
Failures leave a new incomplete destination; never reuse or silently delete it.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import stat

_spec=importlib.util.spec_from_file_location("copy_inventory",Path(__file__).with_name("input-inventory.py"))
inventory=importlib.util.module_from_spec(_spec);_spec.loader.exec_module(inventory)
RESERVE=2_000_000_000
INODE_RESERVE=1024
MAX_RECEIPT=64*1024*1024


def pairs(items):
    value={}
    for key,item in items:
        if key in value:raise ValueError("duplicate inventory JSON key")
        value[key]=item
    return value


def receipt(path,pin):
    if not isinstance(pin,str) or not re.fullmatch("[0-9a-f]{64}",pin):
        raise ValueError("external inventory receipt SHA256 required")
    path=Path(path);parent=directory(path.parent);fd=None
    try:
        fd=os.open(path.name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=parent)
        before=os.fstat(fd)
        if not stat.S_ISREG(before.st_mode) or before.st_nlink!=1 or before.st_size>MAX_RECEIPT:
            raise ValueError("bounded unaliased regular inventory receipt required")
        raw=bytearray()
        while len(raw)<=before.st_size:
            block=os.read(fd,min(262144,before.st_size+1-len(raw)))
            if not block:break
            raw.extend(block)
        after=os.fstat(fd);entry=os.stat(path.name,dir_fd=parent,follow_symlinks=False)
        if (len(raw)!=before.st_size or hashlib.sha256(raw).hexdigest()!=pin or
                inventory.fingerprint(before)!=inventory.fingerprint(after) or
                inventory.fingerprint(after)!=inventory.fingerprint(entry)):
            raise ValueError("inventory receipt pin mismatch or drift")
        return json.loads(raw,object_pairs_hook=pairs)
    finally:
        if fd is not None:os.close(fd)
        os.close(parent)


def directory(path,ancestry=None):
    raw=os.fspath(path)
    if not raw.startswith("/") or any(x in (".","..") for x in raw.split("/")):
        raise ValueError("absolute directory without dot components required")
    fd=os.open("/",os.O_RDONLY|os.O_DIRECTORY)
    try:
        if ancestry is not None:ancestry.append((os.fstat(fd).st_dev,os.fstat(fd).st_ino))
        for name in Path(raw).parts[1:]:
            child=os.open(name,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=fd)
            os.close(fd);fd=child
            if ancestry is not None:ancestry.append((os.fstat(fd).st_dev,os.fstat(fd).st_ino))
        return fd
    except BaseException:
        os.close(fd);raise


def capacity(fd,extra=0,inodes=0):
    fs=os.fstatvfs(fd)
    if fs.f_bavail*fs.f_frsize < RESERVE+extra or fs.f_favail < INODE_RESERVE+inodes:
        raise ValueError("input copy disk/inode reserve unavailable")


def metadata(fd,entry):
    current=os.fstat(fd)
    if (current.st_uid,current.st_gid)!=(entry["uid"],entry["gid"]):
        os.fchown(fd,entry["uid"],entry["gid"])
    # New entries stay owner-writable until xattrs are restored. Applying a
    # read-only source mode first would prevent user xattr restoration.
    for key in os.listxattr(fd):
        if key not in entry["xattrs"]:os.removexattr(fd,key)
    for key,value in entry["xattrs"].items():os.setxattr(fd,key,bytes.fromhex(value))
    os.fchmod(fd,entry["mode"])
    os.utime(fd,ns=(entry["mtimeNs"],entry["mtimeNs"]))
    os.fsync(fd)


def relative_parent(root,name):
    parts=name.split("/")
    if any(p in ("",".","..") for p in parts):raise ValueError("unsafe inventory path")
    fd=os.dup(root)
    try:
        for part in parts[:-1]:
            child=os.open(part,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=fd)
            os.close(fd);fd=child
        return fd,parts[-1]
    except BaseException:
        os.close(fd);raise


def prepare(source,receipt_path,pin,destination):
    expected=receipt(receipt_path,pin)
    source,destination=Path(source),Path(destination)
    observed=inventory.inventory(source)
    if observed!=expected:raise ValueError("source differs from pinned complete inventory")
    if (not destination.is_absolute() or destination.name in ("",".","..") or
            destination.is_relative_to(source) or source.is_relative_to(destination)):
        raise ValueError("fresh disjoint absolute destination required")
    ancestry=[]
    parent=directory(destination.parent,ancestry);src=dst=None
    try:
        if os.fstat(parent).st_uid!=os.geteuid():raise ValueError("destination parent must be owned")
        source_dirs={(r["observedIdentity"]["device"],r["observedIdentity"]["inode"])
                     for r in expected["records"] if r["contentMetadata"]["kind"]=="directory"}
        if source_dirs.intersection(ancestry):raise ValueError("destination aliases source directory")
        rows=[r["contentMetadata"] for r in expected["records"]]
        total=sum(r.get("bytes",0) for r in rows)
        capacity(parent,extra=total+len(rows)*8192,inodes=len(rows))
        src=directory(source)
        root_identity=expected["records"][0]["observedIdentity"]
        if (os.fstat(src).st_dev,os.fstat(src).st_ino)!=(root_identity["device"],root_identity["inode"]):
            raise ValueError("source root identity changed")
        os.mkdir(destination.name,0o700,dir_fd=parent)
        dst=os.open(destination.name,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=parent)
        dest_identity=(os.fstat(dst).st_dev,os.fstat(dst).st_ino)
        for record in expected["records"][1:]:
            entry=record["contentMetadata"];name=entry["path"]
            sp=dp=sf=df=None
            try:
                sp,sn=relative_parent(src,name);dp,dn=relative_parent(dst,name)
                capacity(dst)
                if entry["kind"]=="directory":
                    os.mkdir(dn,0o700,dir_fd=dp)
                elif entry["kind"]=="symlink":
                    if os.readlink(sn,dir_fd=sp)!=entry["target"]:raise ValueError("source link changed")
                    os.symlink(entry["target"],dn,dir_fd=dp)
                    info=os.stat(dn,dir_fd=dp,follow_symlinks=False)
                    if (info.st_uid,info.st_gid)!=(entry["uid"],entry["gid"]):
                        os.chown(dn,entry["uid"],entry["gid"],dir_fd=dp,follow_symlinks=False)
                    handle=f"/proc/self/fd/{dp}/{dn}"
                    for key in os.listxattr(handle,follow_symlinks=False):
                        if key not in entry["xattrs"]:os.removexattr(handle,key,follow_symlinks=False)
                    for key,value in entry["xattrs"].items():os.setxattr(handle,key,bytes.fromhex(value),follow_symlinks=False)
                    os.utime(dn,ns=(entry["mtimeNs"],entry["mtimeNs"]),dir_fd=dp,follow_symlinks=False)
                elif entry["kind"]=="file":
                    sf=os.open(sn,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=sp)
                    before=os.fstat(sf);identity=record["observedIdentity"]
                    if not stat.S_ISREG(before.st_mode) or (before.st_dev,before.st_ino,before.st_ctime_ns,before.st_nlink)!=(identity["device"],identity["inode"],identity["ctimeNs"],identity["links"]):
                        raise ValueError("source file identity changed")
                    df=os.open(dn,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600,dir_fd=dp)
                    digest=hashlib.sha256();count=0
                    while count<=entry["bytes"]:
                        block=os.read(sf,min(262144,entry["bytes"]+1-count))
                        if not block:break
                        capacity(dst,extra=len(block)+8192)
                        digest.update(block);count+=len(block)
                        view=memoryview(block)
                        while view:
                            size=os.write(df,view)
                            if size<=0:raise ValueError("short input copy write")
                            view=view[size:]
                        capacity(dst)
                    if count!=entry["bytes"] or digest.hexdigest()!=entry["sha256"] or inventory.fingerprint(before)!=inventory.fingerprint(os.fstat(sf)):
                        raise ValueError("source changed during copy")
                    metadata(df,entry)
                else:raise ValueError("unsupported inventory entry")
                os.fsync(dp)
            finally:
                for fd in (sf,df,sp,dp):
                    if fd is not None:os.close(fd)
        # Restore directory metadata after all children; file creation changes mtime.
        for entry in reversed(rows):
            if entry["kind"]!="directory":continue
            if entry["path"]==".":fd=os.dup(dst)
            else:
                dp,dn=relative_parent(dst,entry["path"])
                try:fd=os.open(dn,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=dp)
                finally:os.close(dp)
            try:metadata(fd,entry)
            finally:os.close(fd)
        if inventory.inventory(source)!=expected:raise ValueError("source drift after copy")
        copied=inventory.inventory(destination)
        if ([r["contentMetadata"] for r in copied["records"]]!=rows or copied["externalHardlinkAliases"] or
                any(r["observedIdentity"]["links"]!=1 for r in copied["records"] if r["contentMetadata"]["kind"]=="file")):
            raise ValueError("copy content or metadata differs")
        check=directory(destination)
        try:
            if (os.fstat(check).st_dev,os.fstat(check).st_ino)!=dest_identity:raise ValueError("destination root replaced")
        finally:os.close(check)
        capacity(dst);os.fsync(dst);os.fsync(parent)
        return {"status":"verified-prepared-input-copy-only","sourceReceiptSha256":pin,
                "contentMetadataSha256":copied["contentMetadataSha256"],
                "destinationObservationSha256":copied["observationSha256"],
                "records":len(rows),"readOnlyMountAuthenticated":False,
                "lifetimeSealed":False,"workerExecutionAuthorized":False,
                "capacityEnforcementAuthenticated":False,
                "boundary":"Full content/metadata copy observation; hardlinks flattened. Non-atomic source and free-space sampling under writer control, not hostile-host or whole-stage resource attestation."}
    finally:
        for fd in (src,dst,parent):
            if fd is not None:os.close(fd)
