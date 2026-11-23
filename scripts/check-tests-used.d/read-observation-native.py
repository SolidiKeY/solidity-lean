"""Opt-in Linux/x86-64 host tracing primitives (H1390 P2).

Raw lifecycle observations are not read certificates. No checker imports this
module. Unsupported tracing/identity/cleanup is unavailable, never a passing run.
The host/kernel/collector are external testing trust, not adversarial attestation.
"""
import ctypes
import math
import hashlib
import os
import platform
import resource
import signal
import struct
import tempfile
import time
from pathlib import Path

LIBC = ctypes.CDLL(None, use_errno=True)
LIBC.ptrace.restype = ctypes.c_long
TRACEME, CONT, SYSCALL = 0, 7, 24
SETOPTIONS, GETEVENTMSG, GET_SYSCALL_INFO = 0x4200, 0x4201, 0x420e
OPTIONS = 1 | 2 | 4 | 8 | 16 | 64 | 0x100000  # syscall, fork/vfork/clone/exec/exit, EXITKILL
WALL = 0x40000000


class Unavailable(RuntimeError):
    pass


def ptrace(request, pid, address=0, data=0):
    ctypes.set_errno(0)
    value = LIBC.ptrace(ctypes.c_uint(request), ctypes.c_int(pid),
                        ctypes.c_void_p(address), data if not isinstance(data, int) else ctypes.c_void_p(data))
    error = ctypes.get_errno()
    if value == -1 and error:
        raise Unavailable('ptrace: ' + os.strerror(error))
    return value


def process_identity(pid):
    """A process lifetime, not just a recyclable PID or a tracee-written nonce."""
    with open('/proc/%d/stat' % pid) as stream:
        fields = stream.read().rsplit(')', 1)[1].split()
    with open('/proc/stat') as stream:
        boot = next(line.strip() for line in stream if line.startswith('btime '))
    namespace = os.stat('/proc/%d/ns/pid' % pid).st_ino
    return '%s:%d:%d:%s' % (boot, namespace, pid, fields[19])


def executable(pid):
    name = '/proc/%d/exe' % pid
    with open(name, 'rb') as stream:
        digest = hashlib.file_digest(stream, 'sha256').hexdigest()
    return dict(path=os.readlink(name), sha256=digest)


def syscall_stop(pid):
    buffer = ctypes.create_string_buffer(128)
    size = ptrace(GET_SYSCALL_INFO, pid, 128, ctypes.byref(buffer))
    raw = buffer.raw
    if size < 24 or struct.unpack_from('<I', raw, 4)[0] != 0xc000003e:
        raise Unavailable('unsupported syscall ABI')
    operation = raw[0]
    if operation == 1 and size >= 80:
        return dict(kind='enter', number=struct.unpack_from('<Q', raw, 24)[0],
                    args=list(struct.unpack_from('<6Q', raw, 32)))
    if operation == 2 and size >= 33:
        return dict(kind='leave', result=struct.unpack_from('<q', raw, 24)[0])
    raise Unavailable('unsupported syscall stop')


def traced_tasks():
    """Only this single-threaded tracer's ptrace-owned tasks, including pending children."""
    result = set()
    for status in Path('/proc').glob('[0-9]*/task/[0-9]*/status'):
        try:
            fields = dict(line.split(':', 1) for line in status.read_text().splitlines() if ':' in line)
            if int(fields.get('TracerPid', '0')) == os.getpid():
                result.add(int(fields['Pid']))
        except (OSError, ValueError, KeyError):
            continue  # disappeared/unrelated process; tracked tasks still require wait ownership
    return result


def trace(command, cwd, environment, *, timeout, max_events, max_output_bytes, observer=None):
    """Follow only our forked child tree. Bounds are explicit caller budgets.

    observer(event, stopped_tid, tasks) runs while that tid is ptrace-stopped;
    other tasks may run. It must not assume all-stop buffer immutability.
    P3's byte adapter must separately refuse unsafe concurrent observations.
    """
    if platform.system() != 'Linux' or platform.machine() != 'x86_64':
        raise Unavailable('unsupported native platform')
    if type(command) not in (list, tuple) or not command or type(command[0]) is not str or not os.path.isabs(command[0]) or any(type(x) is not str or '\0' in x for x in command):
        raise Unavailable('exact absolute executable and argv required')
    if (not os.path.isabs(cwd) or type(timeout) not in (int, float) or not math.isfinite(timeout)
            or timeout <= 0 or type(max_events) is not int or max_events <= 0
            or type(max_output_bytes) is not int or max_output_bytes <= 0):
        raise Unavailable('explicit cwd and finite positive budgets required')
    if len(list(Path('/proc/self/task').iterdir())) != 1 or traced_tasks():
        raise Unavailable('tracer requires exclusive single-threaded child ownership')
    events, tasks, pending, finished = [], {}, {}, {}
    failure = None
    started = time.monotonic()
    with tempfile.TemporaryFile() as output:
        child = os.fork()
        if child == 0:
            try:
                os.chdir(cwd)
                # Applies to both ordinary/instrumented runs when paired later.
                # Reaching the limit is unavailable, never successful evidence.
                resource.setrlimit(resource.RLIMIT_FSIZE, (max_output_bytes, max_output_bytes))
                os.dup2(output.fileno(), 1)
                os.dup2(output.fileno(), 2)
                ptrace(TRACEME, 0)
                os.kill(os.getpid(), signal.SIGSTOP)
                os.execve(command[0], command, environment)
            except BaseException:
                os._exit(126)
        tasks[child] = dict(identity=None, parent=None, running=False, initial_stop=False, wait_owned=True)
        def emit(pid, event):
            if len(events) >= max_events:
                raise Unavailable('native event budget exhausted')
            event.update(sequence=len(events), tid=pid, identity=tasks[pid]['identity'])
            events.append(event)
            if observer is not None:
                observer(event, pid, tasks)
        try:
            # Initial wait is bounded too: a child failing before TRACEME exits.
            status = None
            while time.monotonic() - started < timeout:
                got, current = os.waitpid(child, os.WNOHANG | WALL)
                if got:
                    status = current
                    break
                time.sleep(0.001)
            if status is not None and (os.WIFEXITED(status) or os.WIFSIGNALED(status)):
                tasks[child]['wait_owned'] = False
            if status is None or not os.WIFSTOPPED(status) or os.WSTOPSIG(status) != signal.SIGSTOP:
                raise Unavailable('initial child trace stop unavailable')
            tasks[child]['identity'] = process_identity(child)
            ptrace(SETOPTIONS, child, 0, OPTIONS)
            emit(child, dict(kind='start', parent=None))
            ptrace(SYSCALL, child)
            tasks[child]['running'] = True
            while tasks:
                if time.monotonic() - started >= timeout:
                    raise Unavailable('native trace timeout')
                if os.fstat(output.fileno()).st_size >= max_output_bytes:
                    raise Unavailable('native output budget exhausted')
                progress = False
                for pid in list(tasks):
                    got, status = os.waitpid(pid, os.WNOHANG | WALL)
                    if not got:
                        continue
                    progress = True
                    tasks[pid]['running'] = False
                    if os.WIFEXITED(status) or os.WIFSIGNALED(status):
                        tasks[pid]['wait_owned'] = False  # consumed before any fallible callback
                        result = dict(exit=os.WEXITSTATUS(status) if os.WIFEXITED(status) else None,
                                      signal=os.WTERMSIG(status) if os.WIFSIGNALED(status) else None)
                        emit(pid, dict(kind='exit', **result))
                        finished[pid] = result
                        del tasks[pid]
                        pending.pop(pid, None)
                        continue
                    if not os.WIFSTOPPED(status):
                        raise Unavailable('unrecognized wait state')
                    stop, event = os.WSTOPSIG(status), status >> 16
                    delivered_signal = 0
                    if event in (1, 2, 3):
                        message = ctypes.c_ulonglong()
                        ptrace(GETEVENTMSG, pid, 0, ctypes.byref(message))
                        descendant = message.value
                        tasks[descendant] = dict(identity=None, parent=pid, running=False, initial_stop=True)
                        tasks[descendant]['identity'] = process_identity(descendant)
                        emit(pid, dict(kind='child', child=descendant, child_identity=tasks[descendant]['identity']))
                    elif event == 4:
                        # Thread-changing exec requires a separate identity map.
                        if process_identity(pid) != tasks[pid]['identity']:
                            raise Unavailable('exec changed process lifetime')
                        emit(pid, dict(kind='exec', executable=executable(pid)))
                    elif event == 6:
                        emit(pid, dict(kind='exiting'))
                    elif stop == signal.SIGTRAP | 0x80:
                        item = syscall_stop(pid)
                        if item['kind'] == 'enter':
                            pending[pid] = item
                        else:
                            entry = pending.pop(pid, None)
                            # New children can begin with a clone return; no
                            # source/byte credit is inferred without its entry.
                            if entry is not None:
                                item.update(number=entry['number'], args=entry['args'], enter_sequence=entry['sequence'])
                        emit(pid, item)
                    elif stop == signal.SIGSTOP:
                        if not tasks[pid]['initial_stop']:
                            raise Unavailable('unexpected group stop')
                        tasks[pid]['initial_stop'] = False
                    else:
                        delivered_signal = stop
                        emit(pid, dict(kind='signal', signal=stop))
                    ptrace(SYSCALL, pid, 0, delivered_signal)
                    tasks[pid]['running'] = True
                if not progress:
                    time.sleep(0.001)
        except (Unavailable, OSError, ChildProcessError) as error:
            failure = str(error)
        finally:
            # A fork can already belong to ptrace while its parent event is
            # pending. Discover those children before killing/reaping, including
            # provisional tasks whose /proc lifetime read failed. Tracer ownership
            # plus our exclusive wait ownership prevents signaling recycled PIDs.
            deadline = time.monotonic() + 2
            first_sweep = True
            while first_sweep or time.monotonic() < deadline:
                first_sweep = False
                owned = traced_tasks()
                if child in tasks and tasks[child].get('wait_owned'):
                    owned.add(child)
                for pid in owned:
                    tasks.setdefault(pid, dict(identity=None))
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                for pid in list(tasks):
                    try:
                        got, status = os.waitpid(pid, os.WNOHANG | WALL)
                        if got and (os.WIFEXITED(status) or os.WIFSIGNALED(status)):
                            del tasks[pid]
                        elif got and os.WIFSTOPPED(status):
                            if status >> 16 in (1, 2, 3):
                                message = ctypes.c_ulonglong()
                                ptrace(GETEVENTMSG, pid, 0, ctypes.byref(message))
                                tasks.setdefault(message.value, dict(identity=None))
                            ptrace(CONT, pid, 0, signal.SIGKILL)
                    except ChildProcessError:
                        # A reaped initial failure is safe only if no ptrace task remains.
                        if pid not in traced_tasks():
                            tasks.pop(pid, None)
                    except Unavailable:
                        pass
                if not tasks and not traced_tasks():
                    break
                time.sleep(0.001)
        output.seek(0)
        log = output.read(max_output_bytes + 1)
        if len(log) >= max_output_bytes:
            failure = 'native output budget exhausted'
            log = log[:max_output_bytes]
    if tasks or traced_tasks():
        failure = 'owned child cleanup unconfirmed'
    return dict(status='unavailable' if failure else 'observed', reason=failure,
                command=command, events=events, result=finished.get(child),
                cleanup_confirmed=not tasks and not traced_tasks(), stdout=log)

# P3 raw byte capture; independent replay/context review are separate stages.
import base64
import stat


class ByteCapture:
    """Capture only fully traced single-task, private-memory regular-file reads.

    Concurrent descendants, shared memory and unsupported asynchronous reads
    remain unavailable. In particular this does not claim general Node support.
    Native/Node stay in the assignment; unsupported observations are not non-use.
    """
    def __init__(self, targets, *, max_capture_bytes):
        if type(max_capture_bytes) is not int or max_capture_bytes <= 0:
            raise Unavailable('explicit positive capture budget required')
        self.targets, self.descriptors, self.records = {}, {}, []
        self.reasons, self.used, self.limit = set(), 0, max_capture_bytes
        self.exec_seen = set()
        self.iovecs = {}
        for name in targets:
            path = Path(name)
            if not path.is_absolute() or str(path.resolve()) != name:
                raise Unavailable('target must be an exact absolute path without symlinks')
            info = path.lstat()
            if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1 or info.st_size > max_capture_bytes:
                raise Unavailable('target is not bounded owned regular bytes')
            opened, data = self.snapshot(path, max_capture_bytes)
            if (opened.st_dev, opened.st_ino) != (info.st_dev, info.st_ino) or len(data) != info.st_size:
                raise Unavailable('target changed during bounded snapshot')
            self.targets[name] = dict(device=info.st_dev, inode=info.st_ino, bytes=len(data),
                                      sha256=hashlib.sha256(data).hexdigest())
        if not self.targets or len(self.targets) != len(targets):
            raise Unavailable('nonempty distinct targets required')

    def memory(self, pid, address, size):
        if size < 0 or self.used + size > self.limit:
            raise Unavailable('returned-byte capture budget exhausted')
        with open('/proc/%d/mem' % pid, 'rb', buffering=0) as stream:
            data = os.pread(stream.fileno(), size, address)
        if len(data) != size:
            raise Unavailable('incomplete stopped-task memory capture')
        return data

    def fd(self, pid, number):
        name = '/proc/%d/fd/%d' % (pid, number)
        path = os.readlink(name)
        info = os.stat(name)
        with open('/proc/%d/fdinfo/%d' % (pid, number)) as stream:
            fields = dict(line.split(':', 1) for line in stream if ':' in line)
        return path, info, int(fields['pos']), int(fields['flags'], 8)

    def __call__(self, event, pid, tasks):
        kind, sequence = event['kind'], event['sequence']
        if kind == 'child':
            self.reasons.add('concurrent or shared descendants unsupported')
        if kind == 'exec':
            if pid in self.exec_seen:
                self.reasons.add('multiple exec source association unsupported')
            self.exec_seen.add(pid)
        if pid not in self.exec_seen:
            return
        if kind in ('exit', 'exiting'):
            for key, descriptor in list(self.descriptors.items()):
                if key[0] == pid:
                    self.close(key, sequence)
            return
        if kind == 'enter' and event['number'] == 19:
            self.iovecs.pop(pid, None)
            args = event['args']
            if (pid, args[0]) in self.descriptors and len(tasks) == 1 and not self.reasons:
                if args[2] > 1024:
                    raise Unavailable('unsupported iovec count')
                raw = self.memory(pid, args[1], args[2] * 16)
                vectors = [struct.unpack_from('<QQ', raw, i * 16) for i in range(args[2])]
                ranges = sorted((a, a + n) for a, n in vectors if n)
                if any(end >= 2**64 for _, end in ranges) or any(x[1] > y[0] for x, y in zip(ranges, ranges[1:])):
                    raise Unavailable('overlapping or overflowing readv buffers')
                self.iovecs[pid] = vectors
                event['entry_iovecs'] = vectors
        if kind != 'leave' or 'number' not in event:
            return
        number, args, result = event['number'], event['args'], event['result']
        if result < 0:
            return
        # A supported read may not borrow an unobserved mutable address space.
        if number in (30, 101, 206, 207, 208, 209, 210, 311, 425, 426, 427, 436) or number == 9 and args[3] & 1:
            self.reasons.add('shared memory or asynchronous memory modification unsupported')
        if number in (76, 77, 82, 83, 84, 86, 87, 88, 258, 263, 264, 265, 266, 316):
            self.reasons.add('path or inode mutation during observation')
        destinations = {16: 0, 1: 0, 18: 0, 20: 0, 296: 0, 328: 0, 285: 0, 40: 0, 275: 2, 276: 1, 326: 2}
        if number in destinations:
            try:
                _, info, _, _ = self.fd(pid, args[destinations[number]])
                if any((info.st_dev, info.st_ino) == (t['device'], t['inode']) for t in self.targets.values()):
                    self.reasons.add('descriptor operation may mutate pinned target, even if later restored')
            except OSError:
                self.reasons.add('successful mutation has unresolved descriptor')
        if number in (2, 257, 437):
            key = (pid, result)
            if key in self.descriptors:
                self.close(key, sequence)
            try:
                path, info, _, flags = self.fd(pid, result)
            except OSError:
                return
            if path not in self.targets:
                return
            target = self.targets[path]
            if (info.st_dev, info.st_ino) != (target['device'], target['inode']) or flags & 3:
                self.reasons.add('target object replaced or opened writable')
                return
            self.descriptors[key] = dict(target=path, opened=sequence, records=[])
        if number == 3:
            self.close((pid, args[0]), sequence)
        if number in (32, 33, 292) or number == 72 and args[1] in (0, 1030):
            source_key, destination_key = (pid, args[0]), (pid, result)
            if source_key != destination_key:
                source = self.descriptors.get(source_key)
                self.close(destination_key, sequence)
                if source is not None:
                    self.descriptors[destination_key] = dict(target=source['target'], opened=sequence, records=[])
        if number not in (0, 17, 19):
            return
        key = (pid, args[0])
        descriptor = self.descriptors.get(key)
        if descriptor is None:
            return
        if self.used + result > self.limit:
            raise Unavailable('returned-byte capture budget exhausted')
        if len(tasks) != 1 or self.reasons:
            self.reasons.add('read lacks exclusive supported task context')
            return
        path, info, position, flags = self.fd(pid, args[0])
        target = self.targets[descriptor['target']]
        if path != descriptor['target'] or (info.st_dev, info.st_ino) != (target['device'], target['inode']):
            raise Unavailable('read descriptor identity changed')
        if number == 19:
            vectors = self.iovecs.pop(pid, None)
            if vectors is None:
                raise Unavailable('readv lacks entry descriptor snapshot')
            remaining, parts, requested = result, [], 0
            for address, count in vectors:
                requested += count
                take = min(remaining, count)
                if take:
                    parts.append(self.memory(pid, address, take))
                remaining -= take
            if remaining:
                raise Unavailable('readv return exceeds requested vectors')
            data = b''.join(parts)
        else:
            requested = args[2]
            if result > requested:
                raise Unavailable('read return exceeds request')
            data = self.memory(pid, args[1], result)
        if requested == 0:
            return  # zero-length no-op is not an empty-file EOF observation
        offset = args[3] if number == 17 else position - result
        if offset < 0 or offset + result > target['bytes']:
            raise Unavailable('returned range outside pinned object')
        record = dict(target=path, sequence=sequence, open_sequence=descriptor['opened'],
                      close_sequence=None, task=event['identity'], fd=args[0],
                      fd_generation=descriptor['opened'], device=info.st_dev, inode=info.st_ino,
                      offset=offset, bytes=result, requested=requested,
                      data=base64.b64encode(data).decode('ascii'), sha256=hashlib.sha256(data).hexdigest())
        self.used += len(data)
        self.records.append(record)
        descriptor['records'].append(record)

    def close(self, key, sequence):
        descriptor = self.descriptors.pop(key, None)
        if descriptor is not None:
            for record in descriptor['records']:
                record['close_sequence'] = sequence

    def snapshot(self, path, size):
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        with os.fdopen(fd, 'rb') as stream:
            info = os.fstat(stream.fileno())
            if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
                raise Unavailable('snapshot object is not an owned regular file')
            return info, stream.read(size + 1)

    def post_digest(self, path, size):
        _, data = self.snapshot(path, size)
        return hashlib.sha256(data).hexdigest()

    def finish(self, trace_result):
        for name, target in self.targets.items():
            try:
                path = Path(name)
                info = path.lstat()
                if (str(path.resolve()) != name or not stat.S_ISREG(info.st_mode) or info.st_nlink != 1
                        or (info.st_dev, info.st_ino) != (target['device'], target['inode'])
                        or info.st_size != target['bytes']
                        or self.post_digest(path, target['bytes']) != target['sha256']):
                    self.reasons.add('post-observation target identity changed')
            except (OSError, Unavailable):
                self.reasons.add('post-observation target unavailable')
        if trace_result['status'] != 'observed' or not trace_result['cleanup_confirmed']:
            self.reasons.add('incomplete trace or cleanup')
        if self.descriptors:
            self.reasons.add('descriptor lifetime unclosed')
        if any(not any(r['target'] == name for r in self.records) for name in self.targets):
            self.reasons.add('no supported target read observed')
        return dict(status='unavailable' if self.reasons else 'captured', reasons=sorted(self.reasons),
                    targets=self.targets, records=self.records)
