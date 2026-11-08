"""Guard H127 before/after arms against shared or unmatched initial cache copies.

Preparation under caller writer-lease/resource/deadline supervision only.
Copies inert bytes, never accepts a cached verdict or launches a worker. A failed
attempt leaves an incomplete fresh envelope; it cannot be reused as a pair.
Content/metadata equality is not physical or page-cache equivalence.
"""
import sys
sys.dont_write_bytecode=True
import importlib.util
import os
from pathlib import Path

spec=importlib.util.spec_from_file_location("pair_copy",Path(__file__).with_name("input-copy.py"))
copy=importlib.util.module_from_spec(spec);spec.loader.exec_module(copy)
ARMS=("before","after")


def prepare(source,receipt,pin,envelope):
    source,envelope=Path(source),Path(envelope)
    expected=copy.receipt(receipt,pin)
    if copy.inventory.inventory(source)!=expected:
        raise ValueError("cache source differs from pinned inventory")
    if (not envelope.is_absolute() or envelope.name in ("",".","..") or
            envelope.is_relative_to(source) or source.is_relative_to(envelope)):
        raise ValueError("fresh disjoint cache envelope required")
    ancestry=[];parent=copy.directory(envelope.parent,ancestry);root=None
    try:
        directories={(r["observedIdentity"]["device"],r["observedIdentity"]["inode"])
                     for r in expected["records"] if r["contentMetadata"]["kind"]=="directory"}
        if directories.intersection(ancestry):raise ValueError("cache envelope aliases source")
        if os.fstat(parent).st_uid!=os.geteuid():raise ValueError("cache parent must be owned")
        rows=[r["contentMetadata"] for r in expected["records"]]
        total=sum(r.get("bytes",0) for r in rows)
        copy.capacity(parent,extra=2*total+2*len(rows)*8192,inodes=2*len(rows)+3)
        os.mkdir(envelope.name,0o700,dir_fd=parent)
        root=os.open(envelope.name,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=parent)
        identity=(os.fstat(root).st_dev,os.fstat(root).st_ino)
        observations={}
        for arm in ARMS:
            os.mkdir(arm,0o700,dir_fd=root)
            arm_path=envelope/arm
            copy.prepare(source,receipt,pin,arm_path/"cache")
            observations[arm]=copy.inventory.inventory(arm_path/"cache")
        identities=[]
        for arm in ARMS:
            observed=copy.inventory.inventory(envelope/arm/"cache")
            if observed!=observations[arm] or [r["contentMetadata"] for r in observed["records"]]!=rows:
                raise ValueError("cache arm changed or initial metadata differs")
            identities.append({(r["observedIdentity"]["device"],r["observedIdentity"]["inode"]) for r in observed["records"]})
        if identities[0].intersection(identities[1]):raise ValueError("cache arms share storage identities")
        if copy.inventory.inventory(source)!=expected:raise ValueError("cache input changed during pairing")
        current=copy.directory(envelope)
        try:
            if (os.fstat(current).st_dev,os.fstat(current).st_ino)!=identity:
                raise ValueError("cache envelope replaced")
        finally:os.close(current)
        copy.capacity(root);os.fsync(root);os.fsync(parent)
        return {"status":"prepared-cache-pair-only","sourceReceiptSha256":pin,
                "initialContentMetadataSha256":expected["contentMetadataSha256"],
                "arms":{arm:{"path":str(envelope/arm/"cache"),"observationSha256":observations[arm]["observationSha256"]} for arm in ARMS},
                "physicalCacheEquivalenceAuthenticated":False,"writableCacheMounted":False,
                "lifetimeSealed":False,"workerExecutionAuthorized":False,
                "boundary":"Initial file content/metadata and disjoint identity observations only. No cache-hit/verdict acceptance, physical/page-cache equivalence, mounting, execution or benchmark measurement."}
    finally:
        if root is not None:os.close(root)
        os.close(parent)
