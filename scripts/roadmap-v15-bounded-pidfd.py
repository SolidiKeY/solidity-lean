#!/usr/bin/env python3
"""V15 verified terminal-process observation; original observe runner unchanged.
Only a previously bound serial process with kernel-confirmed termination can
retire a stale blank-command, zombie, or missing ps row. Live/unknown/unobservable cases reject.
"""
import importlib.util,json,os,re,select,sys,time
from pathlib import Path
spec=importlib.util.spec_from_file_location("v15_observe_base",Path(__file__).with_name("roadmap-v15-bounded-observe.py"))
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
GuardError=base.GuardError
SDK=Path('/workspace/.setup/tools/lean-4.24.0-linux/bin/lean').resolve()

def proc_identity(pid):
    raw=(Path('/proc')/str(pid)/'stat').read_text()
    number,rest=raw.split(' (',1);comm,tail=rest.rsplit(') ',1);fields=tail.split()
    if int(number)!=int(pid) or len(fields)<20:raise GuardError('invalid process identity')
    return dict(pid=int(pid),comm=comm,state=fields[0],start=int(fields[19]))

def proc_launch(pid):
    ident=proc_identity(pid)
    ident['argv']=[x.decode() for x in (Path('/proc')/str(pid)/'cmdline').read_bytes().split(b'\0') if x]
    ident['exe']=str((Path('/proc')/str(pid)/'exe').resolve(strict=True))
    return ident

def kernel_dead(fd, timeout_ms=0):
    poll=select.poll();poll.register(fd,select.POLLIN)
    events=poll.poll(timeout_ms)
    if not events:return False
    if len(events)!=1 or events[0][0]!=fd:raise GuardError('invalid pidfd event')
    mask=events[0][1]
    if mask & (select.POLLERR|select.POLLNVAL) or not mask & select.POLLIN:
        raise GuardError('unverifiable pidfd status')
    return True

class TerminalTracker:
    def __init__(self,journal,exe=SDK,comm='lean',identity=proc_identity,launch=proc_launch,
                 opener=os.pidfd_open,dead=kernel_dead,closer=os.close,wait_dead=None):
        self.journal=journal;self.exe=str(Path(exe).resolve());self.comm=comm
        self.identity=identity;self.launch=launch;self.opener=opener;self.dead=dead;self.closer=closer;self.bound={}
        self.wait_dead=wait_dead or (lambda fd: kernel_dead(fd, 50))
    def record(self,event,**data):self.journal(dict(event=event,**data))
    def bind(self,pid,argv):
        first=self.launch(pid)
        if first['comm']!=self.comm or first['exe']!=self.exe or '-j1' not in first['argv'] or ' '.join(first['argv'])!=argv:
            raise GuardError('process launch identity/serial flags inconsistent')
        fd=self.opener(int(pid),0)
        try:
            second=self.launch(pid)
            if any(first[k]!=second[k] for k in ('pid','comm','start','argv','exe')) or second['state'] in ('Z','X','x') or self.dead(fd):raise GuardError('process changed during pidfd binding')
        except Exception:
            self.closer(fd);raise
        self.bound[pid]=dict(fd=fd,identity=first)
        self.record('pidfd-bound',pid=pid,identity=first)
    def terminated(self,pid,allow_wait=False,retain=False):
        entry=self.bound.get(pid)
        if entry is None:raise GuardError('unbound blank-command process')
        if not self.dead(entry['fd']):
            if not allow_wait:raise GuardError('blank-command process is not kernel-terminal')
            # ps may lose a row or report Z/Zl before pidfd exit readiness.
            # Wait at most50ms on the already identity-bound kernel handle; no
            # workload is resumed or blank/live process accepted on timeout.
            self.record('terminal-wait',pid=pid,timeoutMs=50)
            if not self.wait_dead(entry['fd']):raise GuardError('blank-command process is not kernel-terminal')
            if not self.dead(entry['fd']):raise GuardError('terminal readiness not confirmed')
        try:current=self.identity(pid)
        except FileNotFoundError:current=None
        if current is not None and (current['start']!=entry['identity']['start'] or current['comm']!=self.comm or current['state'] not in ('Z','X','x')):
            raise GuardError('terminal PID reused or still live')
        self.record('kernel-terminal',pid=pid,bound=entry['identity'],current=current,pidfdReadable=True)
        # Retain verified zombie bindings while their ps rows persist. Every
        # subsequent observation rechecks readiness and terminal identity.
        if not retain:self.closer(entry['fd']);del self.bound[pid]
    def snapshot(self,top):
        rows=top.splitlines()
        if not rows or rows[0].split()!=['PID','ELAPSED','RSS','STAT','COMMAND','COMMAND']:
            raise GuardError('invalid terminal-observation snapshot')
        kept=[rows[0]];seen=set()
        for row in rows[1:]:
            parts=row.split(None,5)
            if len(parts)!=6:raise GuardError('invalid terminal-observation row')
            pid,elapsed,rss,stat,comm,argv=parts
            if comm!=self.comm:kept.append(row);continue
            if pid in seen:raise GuardError('duplicate process identity row')
            seen.add(pid)
            if stat.startswith('Z'):
                self.terminated(pid,allow_wait=True,retain=True)
                kept.append(row);continue
            if int(elapsed)>=300:raise GuardError('Lean reached300s limit')
            if argv=='['+self.comm+']' and int(rss)==0:
                self.terminated(pid,allow_wait=True,retain=True)
                continue
            if '-j1' not in argv.split():
                # Preserve the original serial guard: do not excuse any bad argv.
                raise GuardError('Lean missing explicit -j1')
            if pid not in self.bound:self.bind(pid,argv)
            else:
                entry=self.bound[pid]
                try:current=self.launch(pid)
                except FileNotFoundError:
                    # A previously bound process may exit between ps and /proc.
                    # Never extend this fallback to a first binding or other IO errors.
                    if argv!=' '.join(entry['identity']['argv']):
                        raise GuardError('bound snapshot argv changed during disappearance')
                    self.record('bound-launch-disappeared',pid=pid)
                    self.terminated(pid,allow_wait=True,retain=True)
                    continue
                if any(current[k]!=entry['identity'][k] for k in ('pid','comm','start','argv','exe')):
                    raise GuardError('bound process identity changed')
            kept.append(row)
        for pid in list(self.bound):
            if pid not in seen:
                self.terminated(pid,allow_wait=True)
        return '\n'.join(kept)+'\n'
    def close(self):
        for x in self.bound.values():self.closer(x['fd'])
        self.bound.clear()

ACTIVE=[]
class VerifiedLifecycle(base.Lifecycle):
    journal=None
    def __init__(self,cid,start):
        super().__init__(cid,start);self.tracker=TerminalTracker(type(self).journal);ACTIVE.append(self.tracker)
    def observe(self,now,snapshot,top,limits=None):
        if self.admitted and snapshot and snapshot['State']['Running'] and top is not None:
            original=top
            try:top=self.tracker.snapshot(top)
            except Exception as exc:
                self.tracker.record('observation-rejected',rawTop=original,reason=str(exc));raise
            if top!=original:self.tracker.record('verified-terminal-snapshot',rawTop=original,liveTop=top)
        return super().observe(now,snapshot,top,limits)

def run(root,name,command):
    if not re.fullmatch('[a-zA-Z0-9-]+',name):raise ValueError('unsafe label')
    path=Path(root)/(name+'-pidfd.jsonl')
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x') as f:
        def journal(event):f.write(json.dumps(event)+'\n');f.flush()
        VerifiedLifecycle.journal=staticmethod(journal)
        old=base.Lifecycle;base.Lifecycle=VerifiedLifecycle
        try:return base.run(root,name,command)
        finally:
            base.Lifecycle=old
            for tracker in ACTIVE:tracker.close()
            ACTIVE.clear()
if __name__=='__main__':sys.exit(run(*sys.argv[1:]))
