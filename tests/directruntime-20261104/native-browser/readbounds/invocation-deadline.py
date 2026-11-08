"""Guard direct native replay against a milliseconds/seconds budget mixup.

A CLI action runs in one new process group, with the leader kept unreaped until
termination. This is an invocation deadline, not H127 whole-container cleanup or
containment of deliberately escaped descendants. There is no CLI budget waiver.
"""
import os
import signal
import select
import sys
import time
import threading
import traceback

MAXIMUM_NS=300_000_000_000


def execute(action,budget_ns=MAXIMUM_NS):
    if type(budget_ns) is not int or not 0<budget_ns<=MAXIMUM_NS:
        raise ValueError('local invocation budget must be at most300seconds')
    if signal.getsignal(signal.SIGCHLD)!=signal.SIG_DFL:
        raise RuntimeError('unsupported child reaper')
    if threading.current_thread() is not threading.main_thread():
        raise RuntimeError("invocation supervisor requires the main thread")
    deadline=time.monotonic_ns()+budget_ns
    watched=(signal.SIGTERM,signal.SIGHUP,signal.SIGINT)
    old_handlers={number:signal.getsignal(number) for number in watched}
    # Block delivery until fork's child PID is stored. Otherwise termination
    # between fork and assignment can leave a child without a cleanup target.
    old_mask=signal.pthread_sigmask(signal.SIG_BLOCK,watched)
    pid=None;timed_out=False;status=None;pipes={}
    def close_pipe(name):
        descriptor=pipes.pop(name,None)
        if descriptor is not None:os.close(descriptor)
    def interrupted(number,frame):
        raise InterruptedError('native replay supervisor interrupted: '+str(number))
    try:
        for number in watched:signal.signal(number,interrupted)
        pipes['ready_r'],pipes['ready_w']=os.pipe2(os.O_CLOEXEC)
        pipes['go_r'],pipes['go_w']=os.pipe2(os.O_CLOEXEC)
        pid=os.fork()
        if pid==0:
            try:
                close_pipe('ready_r');close_pipe('go_w')
                os.setsid()
                for number in watched:signal.signal(number,signal.SIG_DFL)
                os.write(pipes['ready_w'],b'R');close_pipe('ready_w')
                acknowledgement=os.read(pipes['go_r'],1);close_pipe('go_r')
                if acknowledgement!=b'G':os._exit(1)
                signal.pthread_sigmask(signal.SIG_SETMASK,old_mask)
                action();sys.stdout.flush();sys.stderr.flush()
            except BaseException:
                traceback.print_exc();os._exit(1)
            else:os._exit(0)
        close_pipe('ready_w');close_pipe('go_r')
        while True:
            pending=set(signal.sigpending()).intersection(watched)
            if pending:interrupted(min(pending),None)
            if time.monotonic_ns()>=deadline:
                raise TimeoutError('native replay process-group startup deadline expired')
            if select.select([pipes['ready_r']],[],[],0.005)[0]:
                if os.read(pipes['ready_r'],1)!=b'R':raise RuntimeError('action group startup failed')
                close_pipe('ready_r');break
        if os.getpgid(pid)!=pid:raise RuntimeError('action process group was not established')
        # The action is still waiting for our acknowledgement. A pending signal
        # now kills a known group; before this point closing go_w forbids action.
        signal.pthread_sigmask(signal.SIG_SETMASK,old_mask)
        os.write(pipes['go_w'],b'G');close_pipe('go_w')
        while True:
            if time.monotonic_ns()>=deadline:
                timed_out=True;break
            state=os.waitid(os.P_PID,pid,os.WEXITED|os.WNOHANG|os.WNOWAIT)
            if state is not None:break
            time.sleep(0.005)
    finally:
        # Watched termination signals cannot interrupt kill/reaping. SIGKILL and
        # deliberately escaped descendants still require H127 containment.
        signal.pthread_sigmask(signal.SIG_BLOCK,watched)
        try:
            # Deny startup before attempting any group/leader cleanup.
            for name in list(pipes):close_pipe(name)
            if pid is not None and pid>0:
                # PID remains unreaped: no kill of a reused process group.
                try:os.killpg(pid,signal.SIGKILL)
                except ProcessLookupError:
                    try:os.kill(pid,signal.SIGKILL)
                    except ProcessLookupError:pass
                _,status=os.waitpid(pid,0)
        finally:
            for number,handler in old_handlers.items():signal.signal(number,handler)
            signal.pthread_sigmask(signal.SIG_SETMASK,old_mask)
    if time.monotonic_ns()>=deadline:timed_out=True
    if timed_out:raise TimeoutError('native replay invocation exceeded300second local maximum')
    code=os.waitstatus_to_exitcode(status)
    if code:raise RuntimeError('native replay action failed: '+str(code))
