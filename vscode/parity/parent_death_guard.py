"""Keep an owned Linux build group from outliving its resource supervisor.
Use owned_shell with a new-session child. Its interruptible wait and group KILL
handle foreground payloads and TERM-ignoring children. Guards owned-command
attribution against PID reuse; no environment readback or proof verdict.
"""
import ctypes, os, signal, shlex, time, pathlib
SUPERVISOR_PID = os.getpid()
SHELL_TRAP = "trap 'trap - USR1; kill -KILL -- -$$' USR1\n"
def prepare_child():
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(1, int(signal.SIGUSR1), 0, 0, 0) != 0:
        os._exit(125)
    if os.getppid() != SUPERVISOR_PID:
        os.kill(os.getpid(), signal.SIGKILL)

def owned_shell(argv):
    if not argv:
        raise ValueError("An owned command is required")
    return "set -euo pipefail\n" + SHELL_TRAP + shlex.join(argv) + " &\nowned=$!\nwait \"$owned\"\n"

def result_exit(command_exit, resource_stop, owned_survivors):
    return command_exit if command_exit else (1 if resource_stop or owned_survivors else 0)

def process(pid):
    try:
        text = pathlib.Path('/proc/' + str(pid) + '/stat').read_text()
        fields = text[text.rfind(')') + 2:].split()
        return {'pid': pid, 'birth': fields[19], 'state': fields[0], 'group': int(fields[2]), 'session': int(fields[3])}
    except (FileNotFoundError, ProcessLookupError):
        return None

def command_line(pid, birth):
    """Read only an already-owned birth; refuse reused/disappeared PID attribution."""
    before = process(pid)
    if not before or before['birth'] != birth:
        return None
    try:
        argv = [os.fsdecode(arg) for arg in pathlib.Path('/proc/' + str(pid) + '/cmdline').read_bytes().split(b'\0') if arg]
    except (FileNotFoundError, ProcessLookupError):
        return None
    after = process(pid)
    return argv if after and after['birth'] == birth else None

def exited_without_reaping(pid):
    return os.waitid(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT) is not None

def finish_owned(pid, birth, seen):
    # Caller retains the root zombie until this readback finishes. Its PID/SID
    # cannot be reused, so unsampled members of this private session are owned.
    def live():
        anchor = process(pid)
        if not anchor or anchor['birth'] != birth or anchor['session'] != pid:
            raise RuntimeError('Private build session anchor lost before readback')
        result = []
        for entry in pathlib.Path('/proc').iterdir():
            if not entry.name.isdigit():
                continue
            row = process(int(entry.name))
            if row and row['state'] != 'Z' and (row['group'] == pid or row['session'] == pid or seen.get(row['pid']) == row['birth']):
                result.append(row)
        return result
    before = live()
    deadline = time.monotonic() + 1
    pending = before
    while pending and time.monotonic() < deadline:
        for row in pending:
            current = process(row['pid'])
            if current and current['birth'] == row['birth']:
                try:
                    os.kill(row['pid'], signal.SIGKILL)
                except ProcessLookupError:
                    pass
        time.sleep(0.01)
        pending = live()
    return before, pending

def memory_state():
    fields = {line.split(':', 1)[0]: line.split()[1] for line in pathlib.Path('/proc/meminfo').read_text().splitlines()}
    return {'availableBytes': int(fields['MemAvailable']) * 1024, 'swapTotalBytes': int(fields['SwapTotal']) * 1024}

def resources_allowed(state):
    return state['availableBytes'] >= 12 * 1024**3 and state['swapTotalBytes'] == 0
