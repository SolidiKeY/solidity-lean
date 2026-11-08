#!/usr/bin/env python3
"""Guard H127 cgroup drain checks against kernfs link counts and renamed groups.

Linux cgroup-v2 observations under the existing trusted-kernel/host boundary,
not kernel-build attestation or a cleanup/barrier-release verdict. A live PID,
mandatory files, mount and directory identities must be captured on real FDs;
serialized historical data cannot manufacture a new pin. No cgroup mutation.

Reference: gregkh/linux 2ff600d29ee478d0a8d46ef8a58afb5e038fe692
fs/kernfs/inode.c:kernfs_refresh_inode derives nlink from subdirs+2.
fs/kernfs/dir.c:kernfs_iop_lookup hides inactive nodes.
Documentation/admin-guide/cgroup-v2.rst:[Un]populated Notification defines
populated=0 over the complete subtree. Reference source is not proof that the
running kernel was compiled from those bytes.
"""
import errno
import importlib.util
import os
from pathlib import Path
import stat

spec=importlib.util.spec_from_file_location('h127_retirement_resources',Path(__file__).with_name('kernel-resources.py'))
resources=importlib.util.module_from_spec(spec);spec.loader.exec_module(resources)
FILES=('cgroup.type','cgroup.events','cgroup.procs')


class RetirementError(RuntimeError):
    pass


def core(fd):
    result={}
    for name in FILES:
        try: value=resources._read(fd,name)
        except FileNotFoundError as e:
            if e.errno!=errno.ENOENT:raise
            result[name]={'available':False,'errno':errno.ENOENT}
        else: result[name]={'available':True,'text':value}
    return result


def live_values(values):
    if not all(values[name]['available'] for name in FILES):return None
    domain=values['cgroup.type']['text']
    events=resources.counters(values['cgroup.events']['text'],['populated'])
    if events['populated'] not in (0,1):raise RetirementError('invalid populated counter')
    pids=[resources.number(p) for p in values['cgroup.procs']['text'].splitlines()]
    if any(p<=0 for p in pids) or len(pids)!=len(set(pids)):
        raise RetirementError('invalid or unstable process membership')
    return {'domain':domain,'populated':events['populated'],'pids':pids}


class CgroupPin:
    """Retain live non-root domain identity across observations.

    FDs are duplicated; caller retains its own references. Deactivation requires
    both unchanged parent-name absence and repeated ENOENT for all three core
    files of this previously live pinned cgroup2 inode. Missing paths alone,
    rename/move, mixed file availability and permission/I/O failures never pass.
    A live empty-domain observation additionally uses recursive populated=0.
    Neither result authorizes restart or clears a journal.
    """
    def __init__(self,parent,group,name,pid):
        self.parent=self.group=None
        if not isinstance(name,str) or name in ('','.','..') or '/' in name or any(ord(c)<32 or ord(c)==127 for c in name):
            raise RetirementError('invalid non-root cgroup name')
        if type(pid) is not int or pid<=0:raise RetirementError('requires a live process ID')
        self.name=name;self.clock=resources._clock_module()
        self.mount=resources.mount_record(Path('/proc/self/mountinfo').read_text())
        self.namespace=os.readlink('/proc/self/ns/mnt')
        self.birth_clock=self.clock.capture()
        try:
            self.parent=os.dup(parent);self.group=os.dup(group)
            self.parent_identity=resources._identity(self.parent)
            self.identity=resources._identity(self.group)
            for fd in (self.parent,self.group):
                s=os.fstat(fd)
                if not stat.S_ISDIR(s.st_mode) or [os.major(s.st_dev),os.minor(s.st_dev)]!=self.mount['device']:
                    raise RetirementError('pin is not on observed cgroup2 filesystem')
            first=self.snapshot();second=self.snapshot()
            for row in (first,second):
                values=live_values(row['files'])
                if row['parentEntry']!=self.identity or values is None or values['domain']!='domain' or values['populated']!=1 or pid not in values['pids']:
                    raise RetirementError('live domain/PID capture required')
            self.birth={'pid':pid,'first':first,'second':second}
            self.check_mount()
        except BaseException:self.close();raise

    def close(self):
        for field in ('group','parent'):
            fd=getattr(self,field)
            if fd is not None:os.close(fd);setattr(self,field,None)

    def check_mount(self):
        if self.group is None or self.parent is None:raise RetirementError('pin is closed')
        if self.mount!=resources.mount_record(Path('/proc/self/mountinfo').read_text()) or self.namespace!=os.readlink('/proc/self/ns/mnt'):
            raise RetirementError('cgroup mount/namespace changed')
        if self.parent_identity!=resources._identity(self.parent) or self.identity!=resources._identity(self.group):
            raise RetirementError('pinned directory identity changed')
        if self.clock.capture()['bootId']!=self.birth_clock['bootId']:
            raise RetirementError('boot identity changed')

    def binding(self):
        try: info=os.stat(self.name,dir_fd=self.parent,follow_symlinks=False)
        except FileNotFoundError:return None
        if not stat.S_ISDIR(info.st_mode):raise RetirementError('cgroup parent entry is not a directory')
        result={'device':info.st_dev,'inode':info.st_ino}
        if result!=self.identity:raise RetirementError('cgroup parent entry was replaced')
        return result

    def snapshot(self):
        self.check_mount()
        before=self.binding();files=core(self.group);after=self.binding()
        if before!=after:raise RetirementError('cgroup parent binding changed during capture')
        self.check_mount()
        return {'parentEntry':after,'pinnedIdentity':self.identity,
            'linksInformationalOnly':os.fstat(self.group).st_nlink,'files':files}

    def observe(self):
        start=self.clock.capture();first=self.snapshot();second=self.snapshot();end=self.clock.capture()
        if start['bootId']!=end['bootId']:raise RetirementError('observation crossed boot')
        state='unknown';eligible=False
        absent=all(row['parentEntry'] is None for row in (first,second))
        missing=all(not row['files'][name]['available'] and row['files'][name]['errno']==errno.ENOENT for row in (first,second) for name in FILES)
        if absent and missing:
            state='deactivated-cgroup2-node';eligible=True
        else:
            values=[live_values(row['files']) for row in (first,second)]
            if all(row['parentEntry']==self.identity for row in (first,second)) and all(v is not None and v['domain']=='domain' for v in values):
                if all(v['populated']==0 and not v['pids'] for v in values):
                    state='empty-live-domain';eligible=True
                elif any(v['populated']==1 or v['pids'] for v in values):state='populated-domain'
        return {'state':state,'emptyOrDeactivatedObserved':eligible,'birth':self.birth,
            'first':first,'second':second,'mount':self.mount,'mountNamespace':self.namespace,
            'captureStart':start,'captureEnd':end,'kernelBuildAuthenticated':False,
            'dockerOwnershipAuthenticated':False,'cleanupAccepted':False,'postCreateBarrierReleased':False,
            'boundary':'Point observations under trusted Linux cgroup2 semantics; no hostile-host attestation, Docker ownership, historical recovery, future emptiness, measurement or journal release.'}
