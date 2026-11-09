"""Guard H127 pre-create preparation with repository and pinned journal leases.

No Docker/worker operation or post-create recovery exists here. The trusted
fixed controller must record intent before any future external create operation.
Context exit never clears an active reservation; only explicit, known pre-create
abort can seal it. Admission/check deadlines do not supervise arbitrary caller
code: the future controller must also enforce resource and stage watchdogs.
"""
import sys
sys.dont_write_bytecode=True
import fcntl
import importlib.util
import os
from pathlib import Path
import stat
import time

spec=importlib.util.spec_from_file_location("precreate_journal",Path(__file__).with_name("lifecycle-journal.py"))
journal=importlib.util.module_from_spec(spec);spec.loader.exec_module(journal)
ROOT=Path(__file__).resolve().parents[4]
WRITER=Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
FENCE=ROOT/".lake/native-browser-h127-probe-reservation.json"
ADMISSION_NS=300_000_000_000


class PreparationLease:
    def __init__(self,store,locator,plan_sha256,image_id):
        self._journal=journal.Journal(store,locator)
        self.plan,self.image=plan_sha256,image_id
        self._writer=None;self._owner=None;self._writer_identity=None
        self._identity=None;self._deadline=None;self._entered=False

    @staticmethod
    def _fence():
        try:os.lstat(FENCE)
        except FileNotFoundError:return
        raise journal.Unresolved("existing global probe reservation blocks preparation admission")

    def __enter__(self):
        if self._entered or self._writer is not None:raise journal.JournalError("pre-create lease cannot be reentered")
        self._deadline=time.monotonic_ns()+ADMISSION_NS;self._owner=os.getpid()
        self._fence()
        self._writer=os.open(WRITER,os.O_RDWR|os.O_NOFOLLOW|os.O_NONBLOCK|os.O_CLOEXEC)
        try:
            info=os.fstat(self._writer)
            if not stat.S_ISREG(info.st_mode) or info.st_nlink!=1:raise journal.JournalError("unsafe repository writer lease")
            self._writer_identity=(info.st_dev,info.st_ino)
            while True:
                self._fence()
                if time.monotonic_ns()>=self._deadline:raise TimeoutError("pre-create writer admission expired")
                try:fcntl.flock(self._writer,fcntl.LOCK_EX|fcntl.LOCK_NB);break
                except BlockingIOError:time.sleep(.005)
            self._check_writer()
            self._journal.__enter__()
            if self._journal.read_active() is not None:raise journal.Unresolved("existing journal run blocks preparation")
            if time.monotonic_ns()>=self._deadline:raise TimeoutError("pre-create journal admission expired")
            self._identity=self._journal.reserve(self.plan,self.image)
            if time.monotonic_ns()>=self._deadline:raise TimeoutError("durable reservation exceeded admission deadline")
            self._entered=True
            return self
        except BaseException:
            self.close();raise

    def _check_writer(self):
        if self._writer is None or self._owner!=os.getpid():raise journal.JournalError("controller does not own writer lease")
        info=os.fstat(self._writer);entry=os.stat(WRITER,follow_symlinks=False)
        if (not stat.S_ISREG(entry.st_mode) or info.st_nlink!=1 or
                (info.st_dev,info.st_ino)!=self._writer_identity or
                (entry.st_dev,entry.st_ino)!=self._writer_identity):
            raise journal.JournalError("repository writer lease was replaced")

    def _check(self,admit_work=True):
        self._check_writer();self._fence()
        if not self._entered or self._identity is None:raise journal.JournalError("no active pre-create reservation")
        active=self._journal.read_active()
        if active is None or active["identity"]!=self._identity or active["events"][-1]["state"]!="reserved":
            raise journal.Unresolved("pre-create state changed; recovery required")
        if admit_work and time.monotonic_ns()>=self._deadline:raise TimeoutError("pre-create checked-work admission expired")
        return active

    def observation(self):
        self._check()
        return {"status":"reserved-pre-create-only","identity":dict(self._identity),
                "imageAuthenticated":False,"resourcesAuthenticated":False,
                "containerCreationAuthorized":False,"workerExecutionAuthorized":False,
                "boundary":"Repository and pinned journal lease ownership only; no image/resource/source/sealing/CI/create or worker authorization."}

    def abort_pre_create(self):
        # Cleanup may continue after admission expires, but only while the
        # authenticated state remains reserved. No post-create override exists.
        self._check(admit_work=False)
        receipt=self._journal.seal_pre_create_abort()
        self._identity=None
        return receipt

    def close(self):
        self._journal.__exit__(None,None,None)
        if self._writer is not None:
            # Closing avoids LOCK_UN affecting a parent's inherited description.
            os.close(self._writer);self._writer=None
        self._owner=None

    def __exit__(self,*args):
        self.close()  # Deliberately preserves reserved/ambiguous active records.
