#!/usr/bin/env python3
"""Owned V15 exact-ID admission runner; old sealed runners remain immutable.
No workload runs before limit verification and successful process observation.
The ten-second startup barrier and all post-admission guards are fail closed.
"""
import json, os, re, shlex, subprocess, sys, time, secrets
from pathlib import Path
CAP=12884901888
RESERVE=4294967296 # Human H1,2026-11-02: free RAM +4GiB reserve; cap/swap unchanged.
class GuardError(RuntimeError): pass
class Lifecycle:
    def __init__(self,cid,start):
        self.cid=cid;self.start=start;self.admitted=False;self.observed={}
    def observe(self,now,snapshot,top,limits=None):
        if not self.admitted and now-self.start >= 10: raise GuardError('startup deadline')
        if snapshot is None:
            if self.admitted: raise GuardError('inspect unavailable after release')
            return 'pending'
        if snapshot['Id']!=self.cid: raise GuardError('container identity changed')
        h=snapshot['HostConfig'];env=snapshot['Config']['Env']
        if h['Memory']!=CAP or h['MemorySwap']!=CAP or 'LEAN_NUM_THREADS=1' not in env:
            raise GuardError('container limits/serial configuration mismatch')
        state=snapshot['State']
        if not state['Running']:
            if self.admitted and state['Status']=='exited' and isinstance(state['ExitCode'],int):
                return ('terminal',state['ExitCode'])
            if self.admitted: raise GuardError('unobservable execution state')
            if state['Status'] not in ('created','restarting'): raise GuardError('terminated before admission')
            return 'pending'
        if top is None:
            if self.admitted: raise GuardError('top failure after release')
            return 'pending'
        if len(top.splitlines())<2 or top.splitlines()[0].split()!=['PID','ELAPSED','RSS','STAT','COMMAND','COMMAND']: raise GuardError('invalid/empty process snapshot')
        lean=[]
        for row in top.splitlines()[1:]:
            fields=row.split(None,5)
            if len(fields)!=6: raise GuardError('unparseable process row')
            pid,elapsed,rss,stat,comm,argv=fields
            if comm=='lean' and not stat.startswith('Z'):
                lean.append(pid)
                self.observed[pid]=dict(pid=pid,elapsedSeconds=int(elapsed),rssKiB=int(rss),argv=argv)
                if '-j1' not in argv.split(): raise GuardError('Lean missing explicit -j1')
                if int(elapsed)>=300: raise GuardError('Lean reached300s limit')
        if len(lean)>1: raise GuardError('multiple Lean workers')
        if not self.admitted:
            if lean: raise GuardError('Lean ran before barrier release')
            if limits!=[str(CAP),'0']: return 'pending'
            return 'admit'
        return 'running'

def namespace_pid(pid):
    """Only exact-container stable fence PIDs are read; unavailable data rejects."""
    text=Path('/proc')/str(pid)/'status'
    fields=[line.split()[1:] for line in text.read_text().splitlines() if line.startswith('NSpid:')]
    if len(fields)!=1 or not fields[0]: raise GuardError('namespace PID unavailable')
    result=int(fields[0][-1])
    if result<=0: raise GuardError('invalid namespace PID')
    return result

def completed_workload(marker, token, top, mainPid, mainArg, terminalLoop, moving, pidReader=namespace_pid):
    """Match authenticated fence PIDs/PPIDs, not merely similar command text.
    The marker is emitted by the real fence bash after workload completion.
    Original Lifecycle.observe must already have validated the running snapshot.
    """
    if marker is None: return None
    match=re.fullmatch(re.escape(token)+r" ([0-9]{1,3}) ([1-9][0-9]*) ([1-9][0-9]*)\n",marker)
    if not match: raise GuardError('invalid completion marker')
    code=int(match.group(1));bashNS=int(match.group(2));timeoutNS=int(match.group(3))
    if code>255 or str(code)!=match.group(1): raise GuardError('invalid completion exit')
    if top is None: raise GuardError('completion without observable fence')
    rows=top.splitlines()
    if len(rows)<2 or rows[0].split()!=['PID','PPID','ELAPSED','RSS','STAT','COMMAND','COMMAND']:
        raise GuardError('invalid completion process snapshot')
    if not isinstance(mainPid,int) or mainPid<=0: raise GuardError('missing completion main PID')
    timeoutArg='timeout 10 bash -c '+terminalLoop+' v15-completion '+token+' '+str(code)
    bashArg='bash -c '+terminalLoop+' v15-completion '+token+' '+str(code)
    roleRows={key:[] for key in ['main','timeout','bash','sleep','moving']}
    for row in rows[1:]:
        fields=row.split(None,6)
        if len(fields)!=7: raise GuardError('invalid completion process row')
        pid,ppid,elapsed,rss,stat,comm,argv=fields
        if stat.startswith('Z'): continue
        role=None
        for candidate,expectedComm,expectedArg in [('main','bash',mainArg),('timeout','timeout',timeoutArg),('bash','bash',bashArg),('sleep','sleep','sleep 0.05'),('moving','mv',moving)]:
            if comm==expectedComm and argv==expectedArg:role=candidate;break
        if role is None: raise GuardError('workload/unknown process survived completion marker')
        roleRows[role].append((int(pid),int(ppid)))
    if any(len(roleRows[x])!=1 for x in ['main','timeout','bash']):
        raise GuardError('missing/duplicate completion fence roles')
    if len(roleRows['sleep'])>1 or len(roleRows['moving'])>1:
        raise GuardError('duplicate completion fence helpers')
    main=roleRows['main'][0];timer=roleRows['timeout'][0];bash=roleRows['bash'][0]
    if main[0]!=mainPid or timer[1]!=mainPid or bash[1]!=timer[0]:
        raise GuardError('completion fence parent chain mismatch')
    if any(ppid!=bash[0] for pid,ppid in roleRows['sleep']+roleRows['moving']):
        raise GuardError('unbound completion sleeper/move')
    try:
        correct=(pidReader(mainPid)==1 and pidReader(timer[0])==timeoutNS and pidReader(bash[0])==bashNS)
    except Exception as exc: raise GuardError('completion namespace PID unobservable') from exc
    if not correct: raise GuardError('completion marker PID mismatch')
    return None if roleRows['moving'] else code


def run(root,name,command):
    if not re.fullmatch('[a-zA-Z0-9-]+',name): raise ValueError('unsafe label')
    root=Path(root);root.mkdir(parents=True,exist_ok=True)
    for suffix in ['.log','.json','-processes.json','-monitor-ready','-done','-done.tmp','-completion-ack']:
        if (root/(name+suffix)).exists(): raise FileExistsError(name+suffix)
    for k in ['DOCKER_HOST','DOCKER_CONTEXT','DOCKER_TLS','DOCKER_TLS_VERIFY','DOCKER_CERT_PATH']:os.environ.pop(k,None)
    docker=['docker','--host=unix:///var/run/docker.sock']
    diagnostics=[]
    def call(*a):
        try:
            result=subprocess.run(docker+list(a),capture_output=True,text=True,timeout=2)
            if result.returncode:
                diagnostics.append(dict(operation=a[0],exit=result.returncode,stderr=result.stderr[:4096]))
            return result
        except Exception as exc:
            diagnostics.append(dict(operation=a[0],exception=type(exc).__name__,detail=str(exc)[:4096]))
            raise
    readyPath=root/(name+'-monitor-ready')
    barrier="timeout 10 bash -c "+shlex.quote("until test -e "+shlex.quote(str(readyPath))+"; do sleep 0.05; done")
    donePath=root/(name+'-done');doneTemp=root/(name+'-done.tmp');ackPath=root/(name+'-completion-ack')
    token=secrets.token_hex(16)
    terminalLoop=("printf '%s %s %s %s\\n' "+'"$1" "$2" "$BASHPID" "$PPID" > '+shlex.quote(str(doneTemp))+'; '
        'mv '+shlex.quote(str(doneTemp))+' '+shlex.quote(str(donePath))+'; '
        'until test -e '+shlex.quote(str(ackPath))+'; do sleep 0.05; done')
    # The result marker is written INSIDE the new timeout/bash fence. Its actual
    # namespace PIDs are checked against exact-container host PID/PPID snapshots.
    containerCommand=(barrier+' && ('+command+'); result=$?; echo V15_MEMORY_BYTES; '
        'cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max /sys/fs/cgroup/memory.peak; '
        'timeout 10 bash -c '+shlex.quote(terminalLoop)+' v15-completion '+shlex.quote(token)+' "$result"; fence=$?; '
        'if test "$fence" -ne 0; then exit 124; fi; exit "$result"')
    moving='mv '+str(doneTemp)+' '+str(donePath)
    args=['docker','--host=unix:///var/run/docker.sock','create','--name','v15-'+name,'--network=none','--memory=12g','--memory-swap=12g','--user','1000:1000','-v','/workspace:/workspace','-v','/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:ro','-v','/usr/bin/curl:/usr/bin/curl:ro','-v','/usr/bin/git:/usr/bin/git:ro','-v','/usr/lib/git-core:/usr/lib/git-core:ro','-v','/lib/x86_64-linux-gnu:/lib/x86_64-linux-gnu:ro','-v','/etc/ssl/certs/ca-certificates.crt:/etc/ssl/certs/ca-certificates.crt:ro','-w','/workspace/solidity-lean-v15-p10-help','-e','LEAN_NUM_THREADS=1','-e','SOLKEY_RULES=/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key','-e','CURL_CA_BUNDLE=/etc/ssl/certs/ca-certificates.crt','-e','SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt','-e','XDG_CACHE_HOME=/workspace/.setup/cache','-e','PATH=/workspace/v15-evm-agreement-evidence/p10-help-20261102/bin:/workspace/.setup/tools/lean-4.24.0-linux/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/usr/bin:/bin','ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852','bash','-c',containerCommand]
    start=time.monotonic();cid=None;proc=None;violation=None;events=[];peak=0;terminal=None;life=None;boundMainPid=None
    with (root/(name+'.log')).open('x') as out:
        out.write('COMMAND: '+command+'\n');out.flush()
        try:
            for reclaimPath,reclaimValue in [('/sys/fs/cgroup/memory.reclaim',str(2*1024**3)),('/proc/sys/vm/drop_caches','1')]:
                try:
                    Path(reclaimPath).write_text(reclaimValue)
                    diagnostics.append(dict(pageCacheReclaim=reclaimPath,result='requested'))
                    break
                except OSError as exc:
                    diagnostics.append(dict(pageCacheReclaim=reclaimPath,result='unavailable',detail=str(exc)))
            maxmem=int(Path('/sys/fs/cgroup/memory.max').read_text());current=int(Path('/sys/fs/cgroup/memory.current').read_text())
            diagnostics.append(dict(admissionCurrent=current,admissionMax=maxmem,freeBytes=maxmem-current,reserveBytes=RESERVE,authority='Human H1,2026-11-02'))
            if maxmem-current<RESERVE: raise GuardError('H1 4GiB OS-headroom admission failed')
            ps=subprocess.check_output(['ps','-eo','stat=,comm='],text=True)
            if any(len(x.split())==2 and x.split()[1] in ('lean','lake') and not x.split()[0].startswith('Z') for x in ps.splitlines()):raise GuardError('existing Lean/Lake job; adopt before starting')
            created=subprocess.run(args,capture_output=True,text=True,timeout=10)
            if created.returncode:raise GuardError('docker create failed: '+created.stderr)
            cid=created.stdout.strip()
            if not re.fullmatch('[a-f0-9]{64}',cid):raise GuardError('invalid created ID')
            life=Lifecycle(cid,time.monotonic())
            proc=subprocess.Popen(docker+['start','-a',cid],stdout=out,stderr=subprocess.STDOUT)
            while True:
                now=time.monotonic()
                if now-start>=5400:raise GuardError('original5400s whole-process limit')
                # Sample marker BEFORE top: completion cannot be newer than the process snapshot.
                markerAtStart=None
                if donePath.exists():
                    with donePath.open() as f: markerAtStart=f.read(129)
                    if len(markerAtStart)>128: raise GuardError('oversized completion marker')
                    if not life.admitted: raise GuardError('completion before startup admission')
                ins=call('inspect',cid)
                snapshot=json.loads(ins.stdout)[0] if ins.returncode==0 else None
                top=None;limits=None;topcode=None
                if snapshot and snapshot['State']['Running']:
                    result=call('top',cid,'-eo','pid,etimes,rss,stat,comm,args');topcode=result.returncode
                    top=result.stdout if result.returncode==0 else None
                    if not life.admitted and top is not None:
                        read=call('exec',cid,'cat','/sys/fs/cgroup/memory.max','/sys/fs/cgroup/memory.swap.max')
                        limits=read.stdout.split() if read.returncode==0 else None
                if life.admitted and snapshot and snapshot['State']['Running'] and snapshot['State'].get('Pid')!=boundMainPid:
                    raise GuardError('admitted container main PID changed')
                decision=life.observe(time.monotonic(),snapshot,top,limits)
                events.append(dict(seconds=time.monotonic()-start,cid=cid,running=snapshot['State']['Running'] if snapshot else None,topExit=topcode,limits=limits,decision=decision,admitted=life.admitted))
                if decision=='admit':
                    # Last identity/running snapshot and top succeeded with barrier closed.
                    if time.monotonic()-life.start>=10:raise GuardError('startup deadline before release')
                    boundMainPid=snapshot['State'].get('Pid')
                    if not isinstance(boundMainPid,int) or boundMainPid<=0: raise GuardError('startup main PID unavailable')
                    readyPath.touch(exist_ok=False);life.admitted=True
                    events.append(dict(seconds=time.monotonic()-start,event='barrier-released',cid=cid))
                if isinstance(decision,tuple):
                    # A direct exit is NOT accepted without observing the closed workload fence.
                    raise GuardError('terminal before verified completion fence')
                if markerAtStart is not None:
                    detailed=call('top',cid,'-eo','pid,ppid,etimes,rss,stat,comm,args')
                    if detailed.returncode: raise GuardError('completion detailed top unavailable')
                    resultCode=completed_workload(markerAtStart,token,detailed.stdout,boundMainPid,
                        'bash -c '+containerCommand,terminalLoop,moving)
                    if resultCode is not None:
                        if donePath.read_text()!=markerAtStart: raise GuardError('completion marker changed during observation')
                        # Exact-ID/caps/top already passed above; only fixed waiting shells remain.
                        events.append(dict(event='completion-verified',cid=cid,result=resultCode,
                            seconds=time.monotonic()-start,top=top,detailedTop=detailed.stdout))
                        if time.monotonic()-start>=5400: raise GuardError('original5400s limit before completion ack')
                        ackPath.touch(exist_ok=False)
                        waited=call('wait',cid)
                        if waited.returncode or waited.stdout.strip()!=str(resultCode):
                            raise GuardError('terminal wait disagrees with observed workload result')
                        if time.monotonic()-start>=5400: raise GuardError('original5400s limit after terminal wait')
                        finalRead=call('inspect',cid)
                        if finalRead.returncode: raise GuardError('completion final inspect unavailable')
                        finalSnapshot=json.loads(finalRead.stdout)[0]
                        finalDecision=life.observe(time.monotonic(),finalSnapshot,None)
                        if finalDecision!=('terminal',resultCode):
                            raise GuardError('completion terminal identity/status mismatch')
                        if time.monotonic()-start>=5400: raise GuardError('original5400s limit at final completion')
                        terminal=resultCode
                        events.append(dict(event='completion-terminal',cid=cid,result=resultCode,
                            seconds=time.monotonic()-start))
                        break
                rows=subprocess.check_output(['ps','-eo','rss=,comm='],text=True).splitlines()
                peak=max(peak,sum(int(r.split()[0])*1024 for r in rows if len(r.split())==2 and r.split()[1] in ('lean','lake')))
                time.sleep(.2)
            proc.wait(timeout=2)
            if proc.returncode!=terminal:raise GuardError('attach exit disagrees with container exit')
        except Exception as exc:
            violation=type(exc).__name__+': '+str(exc)
            out.write('V15_PROCESS_GUARD: '+violation+'\n');out.flush()
            if cid and re.fullmatch('[a-f0-9]{64}',cid):
                # Only the exact ID created by this invocation is ever killed.
                try:call('kill',cid)
                except Exception as cleanup:diagnostics.append(dict(cleanupError=str(cleanup)[:4096]))
            if proc:
                try:proc.wait(timeout=2)
                except Exception as cleanup:diagnostics.append(dict(attachCleanupError=str(cleanup)[:4096]))
        finally:
            if cid:
                try:
                    state=call('inspect',cid)
                    if state.returncode:raise GuardError('final inspect failed')
                    finalSnapshot=json.loads(state.stdout)[0]
                    if finalSnapshot['Id']!=cid:raise GuardError('final identity changed')
                    final=finalSnapshot['State']
                    events.append(dict(event='final-state',cid=cid,status=final['Status'],exit=final['ExitCode'],oom=final['OOMKilled']))
                    if final['Running']:raise GuardError('own container still running')
                except Exception as cleanup:
                    diagnostics.append(dict(finalInspectionError=str(cleanup)[:4096]))
                    violation=violation or 'final inspection unavailable/inconsistent'
                # Retain this exact stopped container for evidence; never remove unrelated work.
    code=125 if violation else terminal
    meta=dict(command=command,exit=code,containerId=cid,seconds=time.monotonic()-start,aggregateLeanLakeRssPeakBytes=peak,guardViolation=violation,attachExit=proc.returncode if proc else None,diagnostics=diagnostics,admitted=life.admitted if life else False)
    (root/(name+'-processes.json')).write_text(json.dumps(dict(events=events,observed=list(life.observed.values()) if life else [],guardViolation=violation,diagnostics=diagnostics),indent=2)+'\n')
    (root/(name+'.json')).write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps(meta));return code
if __name__=='__main__':sys.exit(run(*sys.argv[1:]))
