#!/usr/bin/env python3
"""Real Linux Zl lifecycle regression; no Lean, synthetic ps, or guard changes.
A controlled Python child exits only its leader while one worker stays alive.
The production terminal verifier must refuse that group, then retire it after
actual group exit. Python executable override is confined to this test.
"""
import ctypes,hashlib,importlib.util,json,os,select,subprocess,sys,tempfile,threading,time
from pathlib import Path
sys.dont_write_bytecode=True
HEADER='PID ELAPSED RSS STAT COMMAND COMMAND\n'

def child(leader,worker):
    def work():
        end=time.monotonic()+3
        while not worker.exists():
            if time.monotonic()>end:os._exit(3)
            time.sleep(.005)
        os._exit(0)
    threading.Thread(target=work).start()
    print('ready',flush=True)
    while not leader.exists():time.sleep(.005)
    lib=ctypes.CDLL(None);lib.pthread_exit.argtypes=[ctypes.c_void_p];lib.pthread_exit.restype=None
    lib.pthread_exit(None)
    os._exit(4)

def run(out):
    assert sys.platform=='linux' and hasattr(os,'pidfd_open')
    source=Path(__file__).resolve().parents[1]/'scripts/roadmap-v15-bounded-pidfd.py'
    spec=importlib.util.spec_from_file_location('v15_thread_group_monitor',source)
    monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
    events=[];tracker=None;process=None
    result={'kind':'actual controlled thread-group lifecycle, not a reproduction of the former Lean process',
            'monitorSha256':hashlib.sha256(source.read_bytes()).hexdigest()}
    with tempfile.TemporaryDirectory(prefix='v15-thread-group-') as folder:
        leader=Path(folder)/'leader-release';worker=Path(folder)/'worker-release'
        try:
            process=subprocess.Popen([sys.executable,'-B',str(Path(__file__).resolve()),'--child',str(leader),str(worker),'-j1'],stdout=subprocess.PIPE,text=True)
            assert select.select([process.stdout],[],[],1)[0], 'bounded child readiness timeout'
            assert os.read(process.stdout.fileno(),4096)==b'ready\n'
            identity=monitor.proc_launch(process.pid)
            tracker=monitor.TerminalTracker(events.append,exe=sys.executable,comm=identity['comm'])
            tracker.bind(str(process.pid),' '.join(identity['argv']))
            result['initialIdentity']=identity
            leader.touch();deadline=time.monotonic()+1
            while monitor.proc_identity(process.pid)['state']!='Z':
                if time.monotonic()>deadline:raise AssertionError('controlled leader did not become zombie')
                time.sleep(.005)
            raw=subprocess.check_output(['ps','-p',str(process.pid),'-o','pid=,etimes=,rss=,stat=,comm=,args='],text=True,timeout=1)
            fields=raw.split(None,5);assert len(fields)==6 and fields[3].startswith('Z') and 'l' in fields[3] and int(fields[2])==0
            result['realPsRow']=raw;result['tasks']={}
            for path in (Path('/proc')/str(process.pid)/'task').iterdir():
                try:result['tasks'][path.name]=(path/'stat').read_text()
                except FileNotFoundError:pass
            assert any(pid!=str(process.pid) for pid in result['tasks'])
            start=time.monotonic()
            try:tracker.snapshot(HEADER+raw)
            except monitor.GuardError as error:
                assert str(error)=='blank-command process is not kernel-terminal'
                result['rejection']=str(error)
            else:raise AssertionError('live worker group accepted as terminal')
            result['refusalSeconds']=time.monotonic()-start
            assert any(event.get('event')=='terminal-wait' and event['timeoutMs']==50 for event in events)
            assert tracker.bound and not monitor.kernel_dead(tracker.bound[str(process.pid)]['fd'])
            result['nonterminalAfterRejected50msPoll']=True
            worker.touch();result['childExit']=process.wait(timeout=1);assert result['childExit']==0
            result['pidfdReadyAfterRealGroupExit']=monitor.kernel_dead(tracker.bound[str(process.pid)]['fd'])
            assert result['pidfdReadyAfterRealGroupExit']
            tracker.snapshot(HEADER);assert not tracker.bound
            result['terminalRetiredAfterGroupExit']=True
            result['events']=events;result['status']='pass'
        finally:
            worker.touch()
            if tracker:tracker.close()
            if process and process.poll() is None:
                process.terminate()
                try:process.wait(timeout=1)
                except subprocess.TimeoutExpired:process.kill();process.wait(timeout=1)
    if out:
        with Path(out).open('x') as file:json.dump(result,file,indent=2);file.write('\n')
    print('PASS actual Zl/zero-RSS group with live worker refused at50ms; real group exit becomes pidfd-terminal')

if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='--child':child(Path(sys.argv[2]),Path(sys.argv[3]))
    else:run(sys.argv[1] if len(sys.argv)>1 else None)
