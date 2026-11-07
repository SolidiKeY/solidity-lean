#!/usr/bin/env python3
"""Live procfs identity observations; retained JSON consistency is NOT execution proof.

This supplements, never replaces, enforced cgroup/serializer admission. Unknown,
vanished and contradictory identities remain unresolved. No historical reclassification.
"""
import copy
import hashlib
import os
from pathlib import PurePosixPath
import re
import stat
import time

MAX_PROC = 16384
MAX_EXE = 64 * 1024 * 1024
LOCK = '/workspace/scratch/v17-build-process.lock'
FLAGS = dict(kernelValidated=False, semanticPremisesDischarged=False, releaseClosed=False)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def integer(value, positive=False):
    return type(value) is int and value >= (1 if positive else 0)


def parse_stat(raw, pid):
    require(integer(pid, True) and isinstance(raw, str) and len(raw) <= MAX_PROC,
            'invalid PID/stat input')
    require(raw.startswith(str(pid) + ' ('), 'stat PID mismatch')
    close = raw.rfind(') ')
    require(close > 0, 'malformed stat comm')
    fields = raw[close + 2:].split()
    require(len(fields) >= 20 and fields[0] in ('R','S','D','Z','T','t','X','x','K','W','P','I'),
            'malformed stat fields')
    require(fields[19].isdigit() and int(fields[19]) > 0, 'invalid process starttime')
    return dict(pid=pid, state=fields[0], starttime=int(fields[19]))


def parse_cgroup(raw):
    require(isinstance(raw, str) and len(raw) <= MAX_PROC and len(raw.strip().splitlines()) == 1,
            'unsupported cgroup telemetry')
    text = raw.strip()
    require(text.startswith('0::/'), 'requires actual cgroup v2 path')
    path = text[3:]
    require(re.fullmatch(r'/[A-Za-z0-9_./:-]*', path) and '..' not in path.split('/'),
            'malformed cgroup path')
    return path


def fd_stat(fd):
    s = os.fstat(fd)
    require(stat.S_ISREG(s.st_mode), 'executable is not regular')
    return dict(device=s.st_dev, inode=s.st_ino, size=s.st_size,
                mtimeNs=s.st_mtime_ns, ctimeNs=s.st_ctime_ns)


def read_at(fd, name):
    opened = os.open(name, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW, dir_fd=fd)
    try:
        data = os.read(opened, MAX_PROC + 1)
        require(len(data) <= MAX_PROC, 'oversized procfs observation')
        return data.decode('ascii')
    finally:
        os.close(opened)


def observe_process(pid):
    """Read only the fixed kernel procfs root through anchored directory FDs."""
    require(integer(pid, True), 'invalid live PID')
    root = os.open('/proc', os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW)
    process = executable = None
    begin = time.clock_gettime_ns(time.CLOCK_BOOTTIME)
    try:
        process = os.open(str(pid), os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW,
                          dir_fd=root)
        before = read_at(process, 'stat'); group_before = read_at(process, 'cgroup')
        executable = os.open('exe', os.O_RDONLY | os.O_CLOEXEC, dir_fd=process)
        exe_before = fd_stat(executable)
        require(0 < exe_before['size'] <= MAX_EXE, 'unsupported executable size')
        digest = hashlib.sha256(); total = 0
        while True:
            chunk = os.read(executable, 65536)
            if not chunk:
                break
            total += len(chunk); require(total <= MAX_EXE, 'executable grew beyond bound'); digest.update(chunk)
        require(total == exe_before['size'], 'truncated executable observation')
        exe_after = fd_stat(executable)
        try:
            lock = os.stat('fd/9', dir_fd=process)
            lock_info = dict(target=os.readlink('fd/9', dir_fd=process), device=lock.st_dev, inode=lock.st_ino)
        except OSError:
            lock_info = None
        associated = os.open('exe', os.O_RDONLY | os.O_CLOEXEC, dir_fd=process)
        try:
            association_after = fd_stat(associated)
        finally:
            os.close(associated)
        group_after = read_at(process, 'cgroup'); after = read_at(process, 'stat')
        return dict(pid=pid, beginBootNs=begin, endBootNs=time.clock_gettime_ns(time.CLOCK_BOOTTIME),
                    beforeStat=before, afterStat=after, beforeCgroup=group_before, afterCgroup=group_after,
                    executableBefore=exe_before, executableAfter=exe_after,
                    executableAssociationAfter=association_after, executableSha256=digest.hexdigest(), serializerLock=lock_info, **FLAGS)
    finally:
        if executable is not None: os.close(executable)
        if process is not None: os.close(process)
        os.close(root)


def stable_observation(observation):
    require(isinstance(observation, dict), 'missing process observation')
    pid = observation['pid']; a = parse_stat(observation['beforeStat'], pid); b = parse_stat(observation['afterStat'], pid)
    require(a['starttime'] == b['starttime'] and a['state'] not in ('Z','X','x') and b['state'] not in ('Z','X','x'),
            'vanished/reused/exiting process')
    group = parse_cgroup(observation['beforeCgroup'])
    require(group == parse_cgroup(observation['afterCgroup']), 'process changed cgroup')
    first = observation['executableBefore']; second = observation['executableAfter']
    require(isinstance(first, dict) and first == second == observation['executableAssociationAfter'] and set(first) == {'device','inode','size','mtimeNs','ctimeNs'},
            'changed/missing executable FD identity')
    require(all(integer(first[k]) for k in first) and first['inode'] > 0 and 0 < first['size'] <= MAX_EXE,
            'malformed executable FD identity')
    require(isinstance(observation['executableSha256'], str) and re.fullmatch('[0-9a-f]{64}', observation['executableSha256']),
            'missing executable hash')
    require(integer(observation['beginBootNs']) and integer(observation['endBootNs']) and
            observation['endBootNs'] >= observation['beginBootNs'], 'invalid observation clock')
    require(all(observation.get(k) is False for k in FLAGS), 'observation promoted to proof')
    return dict(pid=pid, starttime=a['starttime'], cgroup=group)


def expected_container(inspect, init_observation, lean_sha256):
    """Context comes from the live collector's Docker inspect, not a supplied manifest."""
    require(isinstance(inspect, dict) and isinstance(inspect.get('Id'), str) and
            re.fullmatch('[0-9a-f]{64}', inspect['Id']), 'invalid container identity')
    require(re.fullmatch('/roadmap-v17-[0-9a-f]{32}', inspect.get('Name','')), 'not a task-owned container')
    state = inspect['State']; config = inspect['HostConfig']
    require(state['Running'] is True and integer(state['Pid'], True), 'container not live')
    require(type(config['Memory']) is int and config['Memory'] == 12 * 1024**3 and
            type(config['MemorySwap']) is int and config['MemorySwap'] == config['Memory'] and
            type(config['NanoCpus']) is int and config['NanoCpus'] == 10**9 and config['NetworkMode'] == 'none',
            'container policy mismatch')
    init = stable_observation(init_observation); require(init['pid'] == state['Pid'], 'wrong container init PID')
    parts = PurePosixPath(init['cgroup']).parts
    require(inspect['Id'] in parts or ('docker-' + inspect['Id'] + '.scope') in parts,
            'unsupported/unbound task cgroup path')
    require(isinstance(lean_sha256, str) and re.fullmatch('[0-9a-f]{64}', lean_sha256), 'invalid expected Lean hash')
    lock = os.lstat(LOCK)
    require(stat.S_ISREG(lock.st_mode), 'serializer lock is not a regular file')
    return dict(containerId=inspect['Id'], containerName=inspect['Name'], initPid=init['pid'],
                initStarttime=init['starttime'], cgroup=init['cgroup'], leanSha256=lean_sha256,
                lockDevice=lock.st_dev, lockInode=lock.st_ino)


def validate_expected(expected):
    require(isinstance(expected, dict) and set(expected) == {'containerId','containerName','initPid','initStarttime','cgroup','leanSha256','lockDevice','lockInode'}, 'malformed expected identity')
    require(isinstance(expected['containerId'],str) and re.fullmatch('[0-9a-f]{64}',expected['containerId']) and
            isinstance(expected['containerName'],str) and re.fullmatch('/roadmap-v17-[0-9a-f]{32}',expected['containerName']), 'invalid task binding')
    require(all(integer(expected[k], k != 'lockDevice') for k in ['initPid','initStarttime','lockDevice','lockInode']), 'invalid expected numeric identity')
    group=parse_cgroup('0::'+expected['cgroup']);parts=PurePosixPath(group).parts
    require(expected['containerId'] in parts or ('docker-'+expected['containerId']+'.scope') in parts, 'unbound expected cgroup')
    require(isinstance(expected['leanSha256'],str) and re.fullmatch('[0-9a-f]{64}',expected['leanSha256']), 'invalid expected binary hash')
    return expected


def check_worker(observation, expected, snapshot_begin_boot_ns, clock_ticks):
    """Pure consistency check; retained claims alone NEVER establish live capture."""
    validate_expected(expected)
    identity = stable_observation(observation)
    require(integer(clock_ticks, True) and integer(snapshot_begin_boot_ns), 'invalid snapshot clock')
    # A PID born during/after ps cannot authenticate the earlier ps row. Keep a
    # full tick of separation to reject timestamp-granularity/reuse ambiguity.
    require(clock_ticks == os.sysconf('SC_CLK_TCK') and observation['beginBootNs'] >= snapshot_begin_boot_ns, 'stale/wrong-clock observation')
    before_tick = snapshot_begin_boot_ns * clock_ticks // 10**9
    require(identity['starttime'] < before_tick - 1, 'process not bound before snapshot')
    require(identity['pid'] != expected['initPid'] and identity['starttime'] >= expected['initStarttime'],
            'wrong/reused container process')
    require(identity['cgroup'] == expected['cgroup'] and expected['cgroup'] != '/', 'wrong worker cgroup')
    require(observation['executableSha256'] == expected['leanSha256'], 'wrong executable')
    lock = observation['serializerLock']
    require(isinstance(lock, dict) and set(lock)=={'target','device','inode'} and integer(lock['device']) and integer(lock['inode'],True) and lock == dict(target=LOCK,device=expected['lockDevice'],inode=expected['lockInode']),
            'missing/wrong inherited serializer lock')
    return identity


def check_bracket(before, after, expected, snapshot_begin_boot_ns, snapshot_end_boot_ns, clock_ticks):
    require(integer(snapshot_end_boot_ns) and snapshot_end_boot_ns >= snapshot_begin_boot_ns, 'invalid snapshot window')
    first=check_worker(before,expected,before['beginBootNs'],clock_ticks)
    second=check_worker(after,expected,snapshot_begin_boot_ns,clock_ticks)
    require(before['endBootNs'] <= snapshot_begin_boot_ns and after['beginBootNs'] >= snapshot_end_boot_ns,
            'identities do not bracket snapshot')
    require(first==second and before['executableBefore']==after['executableBefore'] and
            before['executableSha256']==after['executableSha256'] and
            before['serializerLock']==after['serializerLock'], 'process/executable changed across snapshot')
    return second


def capture_pre_context(expected):
    """Read the task cgroup PID list; no global PID search or foreign-process probing."""
    validate_expected(expected)
    directory=os.open('/sys/fs/cgroup',os.O_RDONLY|os.O_DIRECTORY|os.O_CLOEXEC|os.O_NOFOLLOW)
    try:
        for part in PurePosixPath(expected['cgroup']).parts[1:]:
            child=os.open(part,os.O_RDONLY|os.O_DIRECTORY|os.O_CLOEXEC|os.O_NOFOLLOW,dir_fd=directory)
            os.close(directory);directory=child
        text=read_at(directory,'cgroup.procs');tokens=text.split()
        require(tokens and len(tokens)<=128 and all(x.isdigit() and int(x)>0 for x in tokens), 'invalid/oversized task PID inventory')
        pids=[int(x) for x in tokens];require(len(set(pids))==len(pids) and expected['initPid'] in pids,'stale task PID inventory')
        observations={};errors=[]
        for pid in pids:
            try:observations[pid]=observe_process(pid)
            except (ValueError,OSError,KeyError,TypeError) as error:errors.append(dict(pid=pid,error=str(error)))
        return dict(observations=observations,errors=errors,pids=pids,**FLAGS)
    finally:
        os.close(directory)


def enrich_live_sample(original, expected, snapshot_begin_boot_ns, snapshot_end_boot_ns, pre_observations):
    """Collect fresh identities only; preserve every original unknown observation.

    A failed/missing capture leaves the worker unknown. Counts/RSS/limits are
    never reduced or excused. This does not retroactively repair old samples.
    """
    validate_expected(expected)
    sample = copy.deepcopy(original); unknown = sample['unknownLeanProcesses']
    require(all(integer(sample.get(k)) for k in ('rssBytes','leanWorkers','leanSupervisors','leanZombies','leanTransitions','unclassifiedLeanWorkers')), 'invalid original resource fields')
    require(isinstance(unknown,list) and len(unknown) <= 32 and
            len({x['pid'] for x in unknown}) == len(unknown), 'invalid/duplicate unknown process list')
    require(type(sample['leanWorkers']) is int and sample['leanWorkers'] >= 0 and
            type(sample['unclassifiedLeanWorkers']) is int and sample['unclassifiedLeanWorkers'] == len(unknown),
            'contradictory original counts')
    require(all(isinstance(x,dict) and set(x)=={'pid','state','rssBytes','arguments'} and integer(x['pid'],True) and integer(x['rssBytes']) and isinstance(x['state'],str) and x['state'] and x['state'][0] not in ('Z','X','x') and isinstance(x['arguments'],str) and x['arguments'] for x in unknown), 'malformed unknown process')
    require(sum(x['rssBytes'] for x in unknown) <= sample['rssBytes'], 'contradictory process RSS')
    unresolved=[]; observations=[]
    for row in unknown:
        item=dict(original=row)
        try:
            observation=observe_process(row['pid']); item['observation']=observation
            require(isinstance(pre_observations,dict) and row['pid'] in pre_observations,'missing pre-snapshot identity')
            item['beforeObservation']=pre_observations[row['pid']]
            check_bracket(item['beforeObservation'],observation,expected,snapshot_begin_boot_ns,snapshot_end_boot_ns,os.sysconf('SC_CLK_TCK'))
            item['identified']=True; sample['leanWorkers']+=1
        except (ValueError,OSError,KeyError,TypeError) as error:
            item['identified']=False; item['error']=str(error); unresolved.append(row)
        observations.append(item)
    sample['rawUnknownLeanProcesses']=copy.deepcopy(unknown)
    sample['unknownLeanProcesses']=unresolved; sample['unclassifiedLeanWorkers']=len(unresolved)
    sample['processIdentityObservations']=observations
    sample['identityExpected']=copy.deepcopy(expected)
    return sample
