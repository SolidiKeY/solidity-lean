"""Guard H127 resource provenance against mount-root guesses and Docker flags.

Read-only point-in-time PID/cgroup-v2 observer. Kernel PID membership identifies
its group even when a cgroup namespace reports '/'. Visible ancestor constraints
are upper bounds, never complete host-lineage/CI/ownership authentication. No
worker, cgroup creation, budget authorization or cleanup operation is exposed.
"""
import importlib.util
import json
import os
import re
import stat
from fractions import Fraction
from pathlib import Path


class ObservationError(RuntimeError):
    pass


def _clock_module():
    path = Path(__file__).with_name('measurement-clock.py')
    spec = importlib.util.spec_from_file_location('h127_observation_clock', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _directory(path):
    raw = os.fspath(path)
    if not raw.startswith('/') or '..' in raw.split('/'):
        raise ObservationError('unsafe observer filesystem path')
    fd = os.open('/', os.O_RDONLY | os.O_DIRECTORY)
    try:
        for part in Path(raw).parts[1:]:
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = child
        return fd
    except BaseException:
        os.close(fd)
        raise


def _read(fd, name, maximum=262144):
    stream = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=fd)
    try:
        if not stat.S_ISREG(os.fstat(stream).st_mode):
            raise ObservationError('nonregular kernel observation')
        chunks, count = [], 0
        while count <= maximum:
            block = os.read(stream, min(8192, maximum+1-count))
            if not block:
                break
            chunks.append(block)
            count += len(block)
        if count > maximum:
            raise ObservationError('kernel observation exceeds bound')
        return b''.join(chunks).decode('ascii').rstrip('\n')
    finally:
        os.close(stream)


def number(value, maximum=(1 << 64)-1):
    if not isinstance(value, str) or not re.fullmatch(r'0|[1-9][0-9]*', value):
        raise ObservationError('invalid unsigned kernel number')
    result = int(value)
    if result > maximum:
        raise ObservationError('unsupported kernel number range')
    return result


def limit(value):
    return None if value == 'max' else number(value)


def cpu_limit(value):
    fields = value.split()
    if len(fields) != 2:
        raise ObservationError('invalid cpu.max')
    quota, period = limit(fields[0]), number(fields[1])
    if not period or quota == 0:
        raise ObservationError('invalid CPU period/quota')
    return {'quota': quota, 'period': period}


def cpu_set(value):
    intervals, previous = [], -1
    if not value:
        raise ObservationError('empty effective CPU set')
    for field in value.split(','):
        parts = field.split('-')
        if len(parts) not in (1, 2):
            raise ObservationError('invalid CPU interval')
        low = number(parts[0], 1048575)
        high = number(parts[-1], 1048575)
        if low > high or low <= previous:
            raise ObservationError('overlapping or reversed CPU intervals')
        intervals.append([low, high])
        previous = high
    return intervals


def counters(value, required):
    result = {}
    for line in value.splitlines():
        fields = line.split()
        if len(fields) != 2 or not re.fullmatch(r'[a-z_]+', fields[0]) or fields[0] in result:
            raise ObservationError('invalid or duplicate kernel counter')
        result[fields[0]] = number(fields[1])
    if not set(required) <= set(result):
        raise ObservationError('missing required kernel counters')
    return result


def mount_record(text, point='/sys/fs/cgroup'):
    matches = []
    for line in text.splitlines():
        fields = line.split()
        if '-' not in fields:
            raise ObservationError('malformed mountinfo')
        separator = fields.index('-')
        if separator < 6 or len(fields) < separator+4:
            raise ObservationError('short mountinfo')
        unescape = lambda x: re.sub(r'\\(040|011|012|134)', lambda m: chr(int(m[1], 8)), x)
        if unescape(fields[4]) != point:
            continue
        if fields[separator+1] != 'cgroup2':
            raise ObservationError('primary cgroup mount is not v2')
        major_minor = fields[2].split(':')
        if len(major_minor) != 2:
            raise ObservationError('invalid cgroup mount device')
        matches.append({'mountId': number(fields[0]), 'device': list(map(number, major_minor)),
                        'root': unescape(fields[3]), 'point': point,
                        'options': fields[5], 'raw': line})
    if len(matches) != 1:
        raise ObservationError('ambiguous or absent primary cgroup mount')
    return matches[0]


def _identity(fd):
    info = os.fstat(fd)
    return {'device': info.st_dev, 'inode': info.st_ino}


def locate(rootfd, pid, max_groups=4096, max_depth=32):
    """Return pinned ancestor descriptors for the unique direct PID membership.

    Namespace path strings are recorded separately and never used as paths.
    Caller owns returned FDs. Missing/racing/unrecognized groups fail closed.
    """
    found, seen = [], 0
    def visit(fd, stack, depth):
        nonlocal seen
        seen += 1
        if seen > max_groups or depth > max_depth:
            raise ObservationError('cgroup search bound exceeded')
        if _read(fd, 'cgroup.type') != 'domain':
            raise ObservationError('unsupported threaded cgroup layout')
        members = [number(x) for x in _read(fd, 'cgroup.procs').splitlines()]
        if members.count(pid) > 1:
            raise ObservationError('unstable repeated PID membership')
        if pid in members:
            if found:
                raise ObservationError('ambiguous PID membership')
            try:
                for name, parent in stack:
                    found.append((name, os.dup(parent)))
            except BaseException:
                for _, parent in found:os.close(parent)
                found.clear()
                raise
        for name in sorted(os.listdir(fd)):
            item = os.stat(name, dir_fd=fd, follow_symlinks=False)
            if stat.S_ISLNK(item.st_mode):
                raise ObservationError('unexpected cgroup symlink')
            if stat.S_ISDIR(item.st_mode):
                child = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
                try:
                    child_name = stack[-1][0].rstrip('/')+'/'+name
                    visit(child, stack+[(child_name, child)], depth+1)
                finally:
                    os.close(child)
    try:
        visit(rootfd, [('/', rootfd)], 0)
        if not found:
            raise ObservationError('PID membership not found in visible hierarchy')
        return found
    except BaseException:
        for _, fd in found:os.close(fd)
        raise


def constraints(fd):
    kind = _read(fd, 'cgroup.type')
    weight = number(_read(fd, 'cpu.weight'))
    if kind != 'domain' or not 1 <= weight <= 10000:
        raise ObservationError('unsupported cgroup type or CPU weight')
    return {'cgroupType': kind, 'memoryMaxBytes': limit(_read(fd, 'memory.max')),
            'memoryHighBytes': limit(_read(fd, 'memory.high')),
            'swapMaxBytes': limit(_read(fd, 'memory.swap.max')),
            'cpuMax': cpu_limit(_read(fd, 'cpu.max')),
            'cpuBurstMicroseconds': number(_read(fd, 'cpu.max.burst')),
            'cpuWeight': weight,
            'effectiveCpuIntervals': cpu_set(_read(fd, 'cpuset.cpus.effective'))}


def _process(fd, pid):
    raw = _read(fd, 'stat')
    if not raw.startswith(str(pid)+' (') or ')' not in raw:
        raise ObservationError('invalid process stat identity')
    fields = raw[raw.rfind(')')+2:].split()
    if len(fields) < 20:
        raise ObservationError('short process stat')
    group = _read(fd, 'cgroup').splitlines()
    if len(group) != 1 or not group[0].startswith('0::/'):
        raise ObservationError('unsupported process cgroup membership')
    ns = os.open('ns', os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
    try:
        namespaces = {kind: os.readlink(kind, dir_fd=ns) for kind in ['pid', 'mnt', 'cgroup', 'user']}
    finally:
        os.close(ns)
    affinity = sorted(os.sched_getaffinity(pid))
    if not affinity or any(type(cpu) is not int or cpu < 0 for cpu in affinity):
        raise ObservationError('missing or invalid process CPU affinity')
    for kind, handle in namespaces.items():
        if not re.fullmatch(re.escape(kind)+r':\[[0-9]+\]', handle):
            raise ObservationError('invalid kernel namespace handle')
    return {'pid': pid, 'startTicks': number(fields[19]),
            'procDirectory': _identity(fd), 'uid': os.fstat(fd).st_uid,
            'unifiedNamespacePath': group[0][3:], 'namespaces': namespaces,
            'affinity': affinity, 'observedLeaderSchedulingPolicy': os.sched_getscheduler(pid)}


def cpu_configuration(rows):
    """Separate cpuset concurrency from configured fair-class quota ratios.

    Quota credit, period boundaries and burst allow short-interval parallelism.
    This is not a complete scheduling-policy or serial-execution attestation.
    """
    concurrency = min(sum(b-a+1 for a,b in row['constraints']['effectiveCpuIntervals']) for row in rows)
    rates = [Fraction(row['constraints']['cpuMax']['quota'], row['constraints']['cpuMax']['period'])
             for row in rows if row['constraints']['cpuMax']['quota'] is not None]
    rate = min(rates) if rates else None
    return {'visibleCpusetConcurrentCpuUpperBound': concurrency,
            'visibleConfiguredSustainedQuotaRate': None if rate is None else {'numerator': rate.numerator, 'denominator': rate.denominator},
            'cpuTimeBoundary': 'Configured quota/period ratios concern sustained fair-class CPU rate while settings remain fixed, not finite-interval concurrency. Burst credits are recorded per ancestor. Per-thread scheduling and serial execution are not authenticated.'}


def _sample(clock):
    try:
        return clock.capture()
    except clock.ClockError as error:
        raise ObservationError('clock observation unavailable') from error


def observe(pid=None):
    pid = os.getpid() if pid is None else pid
    if type(pid) is not int or pid <= 0:
        raise ObservationError('requires a positive process ID')
    clock = _clock_module(); start = _sample(clock)
    primary = mount_record(Path('/proc/self/mountinfo').read_text())
    rootfd = process = None
    hierarchy = []
    try:
        rootfd = _directory(primary['point'])
        dev = os.fstat(rootfd).st_dev
        if [os.major(dev), os.minor(dev)] != primary['device']:
            raise ObservationError('cgroup mount device changed')
        process = _directory('/proc/'+str(pid))
        identity = _process(process, pid)
        hierarchy = locate(rootfd, pid)
        rows = []
        for path, fd in hierarchy:
            rows.append({'path': path, 'identity': _identity(fd), 'constraints': constraints(fd),
                         'memoryCurrentBytes': number(_read(fd, 'memory.current')),
                         'memoryPeakBytes': number(_read(fd, 'memory.peak')),
                         'swapCurrentBytes': number(_read(fd, 'memory.swap.current')),
                         'memoryEvents': counters(_read(fd, 'memory.events'), ['oom', 'oom_kill']),
                         'cpuStat': counters(_read(fd, 'cpu.stat'), ['usage_usec'])})
        for (_, fd), row in zip(hierarchy, rows):
            if constraints(fd) != row['constraints']:
                raise ObservationError('resource constraints changed during capture')
        if pid not in [number(x) for x in _read(hierarchy[-1][1], 'cgroup.procs').splitlines()]:
            raise ObservationError('PID moved out of observed cgroup')
        if _process(process, pid) != identity or mount_record(Path('/proc/self/mountinfo').read_text()) != primary:
            raise ObservationError('process, affinity, namespace or mount identity changed')
        intervals = rows[-1]['constraints']['effectiveCpuIntervals']
        if any(not any(low <= cpu <= high for low, high in intervals) for cpu in identity['affinity']):
            raise ObservationError('process affinity lies outside observed effective CPU set')
        end = _sample(clock)
        if start['bootId'] != end['bootId']:
            raise ObservationError('boot identity changed')
        return {'status': 'observed', 'process': identity, 'mount': primary,
                'captureStart': start, 'captureEnd': end, 'ancestors': rows,
                **cpu_configuration(rows),
                'completeHostLineageAuthenticated': False, 'dockerOwnershipAuthenticated': False,
                'memoryMetric': 'charged cgroup memory; not aggregate process RSS',
                'boundary': 'Point-in-time, non-atomic kernel observations; hidden ancestors may constrain further. Requires authenticated outer/inner mapping, continuous monitoring and cleanup verifier. No worker or measurement pass.'}
    finally:
        for _, fd in hierarchy:os.close(fd)
        if process is not None:os.close(process)
        if rootfd is not None:os.close(rootfd)


if __name__ == '__main__':
    try:
        print(json.dumps(observe(), sort_keys=True))
    except (OSError, ValueError, ObservationError) as error:
        print(json.dumps({'status': 'unavailable', 'reason': str(error), 'workerExecuted': False}))
        raise SystemExit(2)
