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
                                item.update(number=entry['number'], args=entry['args'])
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
