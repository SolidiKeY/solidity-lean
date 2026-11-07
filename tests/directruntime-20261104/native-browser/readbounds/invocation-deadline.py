"""Guard direct native replay against a milliseconds/seconds budget mixup.

A CLI action runs in one new process group, with the leader kept unreaped until
termination. This is an invocation deadline, not H127 whole-container cleanup or
containment of deliberately escaped descendants. There is no CLI budget waiver.
"""
import os
import signal
import sys
import time
import traceback

MAXIMUM_NS=300_000_000_000


def execute(action,budget_ns=MAXIMUM_NS):
    if type(budget_ns) is not int or not 0<budget_ns<=MAXIMUM_NS:
        raise ValueError('local invocation budget must be at most300seconds')
    if signal.getsignal(signal.SIGCHLD)!=signal.SIG_DFL:
        raise RuntimeError('unsupported child reaper')
    deadline=time.monotonic_ns()+budget_ns
    pid=os.fork()
    if pid==0:
        try:
            os.setsid();action();sys.stdout.flush();sys.stderr.flush()
        except BaseException:
            traceback.print_exc();os._exit(1)
        else:os._exit(0)
    timed_out=False
    try:
        while True:
            if time.monotonic_ns()>=deadline:
                timed_out=True;break
            state=os.waitid(os.P_PID,pid,os.WEXITED|os.WNOHANG|os.WNOWAIT)
            if state is not None:break
            time.sleep(0.005)
    finally:
        # Child PID is reserved until waitpid; no kill of a reused process group.
        try:os.killpg(pid,signal.SIGKILL)
        except ProcessLookupError:
            try:os.kill(pid,signal.SIGKILL)
            except ProcessLookupError:pass
        _,status=os.waitpid(pid,0)
    if time.monotonic_ns()>=deadline:timed_out=True
    if timed_out:raise TimeoutError('native replay invocation exceeded300second local maximum')
    code=os.waitstatus_to_exitcode(status)
    if code:raise RuntimeError('native replay action failed: '+str(code))
