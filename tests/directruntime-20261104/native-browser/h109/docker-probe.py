#!/usr/bin/env python3
"""Guard H127 cleanup against name-only kills and launcher-exit false success.

Fixed sleep probe only. No Lean, arbitrary worker command, mount, cache or proof
budget is exposed. Docker ownership and a pinned cgroup removal are observations
under a trusted local daemon/kernel and exclusive controller, not hostile-host
attestation. The durable post-create journal barrier is deliberately NOT released.
"""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import selectors
import signal
import stat
import subprocess
import time
import threading

DOCKER = Path('/usr/local/bin/docker')
SOCKET = Path('/var/run/docker.sock')
MEMORY = 12 * 1024**3
RESERVE = 4 * 1024**3
LOCK = '/tmp/solidity-lean-feature-groups-20261025/writer.lock'
RESERVATION = Path(__file__).resolve().parents[4]/'.lake/native-browser-h127-probe-reservation.json'
COMMAND = ['-c', 'exec /bin/sleep 60']
RECIPE = 'h127-owned-sleep-probe-v1'
LABEL = 'org.solidity-lean.h127.'
HEX = re.compile(r'[0-9a-f]{64}\Z')


def load(name):
    spec = importlib.util.spec_from_file_location('h127_'+name, Path(__file__).with_name(name+'.py'))
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


journal_module = load('lifecycle-journal')
resources = load('kernel-resources')
clock = load('measurement-clock')


class ProbeError(RuntimeError):
    def __init__(self,message,facts=None):
        super().__init__(message);self.facts={} if facts is None else facts


def exact_hex(value):
    if not isinstance(value, str) or not HEX.fullmatch(value):
        raise ProbeError('requires full lowercase container ID')
    return value


def image_id(value):
    if not isinstance(value, str) or not value.startswith('sha256:'):
        raise ProbeError('requires immutable image ID')
    exact_hex(value[7:]); return value


def digest_file(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(262144), b''): h.update(block)
    return h.hexdigest()


def bounded(argv, env, timeout=15, maximum=4*1024*1024, guard=None):
    """Bound trusted local-client output/time, including its process group.

    Killing a CLI is not container cleanup; a mutating call remains ambiguous
    on timeout, signal, malformed output or I/O failure.
    """
    if signal.getsignal(signal.SIGCHLD) != signal.SIG_DFL:
        raise ProbeError('unsupported concurrent child reaper')
    proc = subprocess.Popen(argv, env=env, stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True,
        close_fds=True)
    chunks = {proc.stdout:bytearray(), proc.stderr:bytearray()}
    start = time.monotonic_ns(); deadline = start + timeout*10**9
    try:
        with selectors.DefaultSelector() as selected:
            for stream in chunks:
                os.set_blocking(stream.fileno(), False)
                selected.register(stream, selectors.EVENT_READ)
            while selected.get_map():
                if guard is not None: guard()
                remaining = deadline-time.monotonic_ns()
                if remaining <= 0: raise ProbeError('Docker client timeout; result unknown')
                for key,_ in selected.select(min(remaining/10**9, 0.1)):
                    part = os.read(key.fd, 65536)
                    if not part: selected.unregister(key.fileobj); continue
                    chunks[key.fileobj].extend(part)
                    if sum(map(len, chunks.values())) > maximum:
                        raise ProbeError('Docker client output bound; result unknown')
            # Keep the leader unreaped until its private process group is killed;
            # killing a numeric group after reaping could hit a reused PID/PGID.
            while os.waitid(os.P_PID,proc.pid,os.WEXITED|os.WNOHANG|os.WNOWAIT) is None:
                if guard is not None: guard()
                if time.monotonic_ns()>=deadline: raise ProbeError('Docker client wait timeout')
                time.sleep(0.01)
        waited=os.waitid(os.P_PID,proc.pid,os.WEXITED|os.WNOWAIT)
        return {'code':waited.si_status if waited.si_code==os.CLD_EXITED else -waited.si_status,
                'stdout':bytes(chunks[proc.stdout]),
                'stderr':bytes(chunks[proc.stderr]), 'elapsedNs':time.monotonic_ns()-start}
    finally:
        # Even an early leader exit must not leave a client helper holding pipes.
        try: os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError: pass
        proc.wait()
        proc.stdout.close(); proc.stderr.close()


class Docker:
    def __init__(self):
        if not stat.S_ISREG(DOCKER.lstat().st_mode):
            raise ProbeError('Docker executable must be a regular file')
        self.binary = digest_file(DOCKER)
        self.socket = self.socket_identity()
        self.boot = clock.boot_id()
        # Preserve platform Docker config/credentials; never inherit endpoint,
        # context or TLS selectors. Every invocation names the local socket.
        self.env = {key:os.environ[key] for key in ('HOME','DOCKER_CONFIG','XDG_CONFIG_HOME') if key in os.environ}
        self.env.update(PATH='/usr/local/bin:/usr/bin:/bin', LC_ALL='C')
        self.trace = []
        self.deadline = None
        self.guard = None
        self.daemon = self.info()

    def socket_identity(self):
        actual = SOCKET.resolve(strict=True); info = actual.stat()
        if not stat.S_ISSOCK(info.st_mode): raise ProbeError('local Docker socket unavailable')
        return {'path':str(actual),'device':info.st_dev,'inode':info.st_ino}

    def local_identity(self):
        if self.boot != clock.boot_id() or self.binary != digest_file(DOCKER) or self.socket != self.socket_identity():
            raise ProbeError('Docker endpoint, boot or client changed')

    def invoke(self, args):
        self.local_identity()
        if self.guard is not None: self.guard()
        remaining = 15 if self.deadline is None else min(15,(self.deadline-time.monotonic_ns())/10**9)
        if remaining<=0: raise ProbeError('Docker phase deadline expired; result unknown')
        result = bounded([str(DOCKER), '--host=unix:///var/run/docker.sock', *args], self.env, timeout=remaining, guard=self.guard)
        self.local_identity()
        self.trace.append({'operation':' '.join(args[:2]), 'exitCode':result['code'],
            'elapsedNs':result['elapsedNs'], 'stdoutSha256':hashlib.sha256(result['stdout']).hexdigest(),
            'stderrSha256':hashlib.sha256(result['stderr']).hexdigest()})
        if result['code'] != 0: raise ProbeError('Docker '+args[0]+' failed; no fallback verdict')
        return result['stdout']

    def info(self):
        raw = self.invoke(['info','--format','[{{json .ID}},{{json .CgroupVersion}},{{json .CgroupDriver}},{{json .ServerVersion}}]'])
        info = json.loads(raw)
        if not isinstance(info,list) or len(info)!=4 or not all(isinstance(x,str) for x in info) or info[1]!='2':
            raise ProbeError('unsupported Docker daemon/cgroup observation')
        return info

    def call(self, args):
        if self.info() != self.daemon: raise ProbeError('Docker daemon identity/configuration changed')
        value = self.invoke(args)
        if self.info() != self.daemon: raise ProbeError('Docker daemon changed during command')
        if self.deadline is not None and time.monotonic_ns()>=self.deadline:
            raise ProbeError('Docker phase deadline overrun')
        return value

    def inspect(self, container):
        exact_hex(container)
        data = json.loads(self.call(['container','inspect',container]))
        if not isinstance(data,list) or len(data)!=1 or not isinstance(data[0],dict):
            raise ProbeError('ambiguous container inspection')
        return data[0]

    def listed(self, filter_value):
        rows = self.call(['container','ls','--all','--quiet','--no-trunc','--filter',filter_value]).decode('ascii').splitlines()
        for row in rows: exact_hex(row)
        if len(rows)!=len(set(rows)): raise ProbeError('duplicate listed container')
        return rows


def labels(identity):
    return {LABEL+'nonce':identity['nonce'],LABEL+'plan':identity['planSha256'],LABEL+'recipe':RECIPE}


def ownership(data, identity, expected):
    exact_hex(expected); image_id(identity['imageId'])
    if not re.fullmatch(r'h127-[0-9a-f]{32}',identity['name']) or identity['name']!='h127-'+identity['nonce']:
        raise ProbeError('invalid reserved name')
    if not HEX.fullmatch(identity['planSha256']): raise ProbeError('invalid plan pin')
    try:
        good = (data['Id']==expected and data['Name']=='/'+identity['name'] and
                data['Image']==identity['imageId'] and
                all(data['Config']['Labels'].get(k)==v for k,v in labels(identity).items()))
    except (KeyError,TypeError,AttributeError) as e: raise ProbeError('missing ownership fields') from e
    if not good: raise ProbeError('foreign or drifted Docker ownership')
    return data


def policy(data, identity, expected, cpu):
    ownership(data, identity, expected)
    try:
        h,c = data['HostConfig'],data['Config']
        checks = [c['User']=='1000:1000',c['Entrypoint']==['/bin/sh'],c['Cmd']==COMMAND,
            c['WorkingDir']=='/',h['ReadonlyRootfs'] is True,h['Privileged'] is False,
            h['NetworkMode']=='none',h['PidMode']=='',h['IpcMode']=='private',h['CgroupnsMode']=='private',
            h['Memory']==MEMORY,h['MemorySwap']==MEMORY,h['NanoCpus']==10**9,h['CpusetCpus']==str(cpu),
            h['PidsLimit']==64,h['CapDrop']==['ALL'],not h['CapAdd'],
            h['SecurityOpt']==['no-new-privileges'],not h['Binds'],not h['Devices'],not h['DeviceRequests'],
            h['RestartPolicy']=={'Name':'no','MaximumRetryCount':0},h['AutoRemove'] is False,
            not data['Mounts'],not h['PortBindings'],not h['Links'],not h['VolumesFrom']]
    except (KeyError,TypeError) as e: raise ProbeError('missing fixed-probe policy fields') from e
    if not all(checks): raise ProbeError('fixed-probe isolation policy mismatch')


def create_args(identity,cpu):
    image_id(identity['imageId'])
    if type(cpu) is not int or cpu<0: raise ProbeError('single CPU pin required')
    # Validate all externally supplied identity syntax before reserving CLI flags.
    exact_hex(identity['planSha256'])
    if identity['name']!='h127-'+identity['nonce'] or not re.fullmatch(r'[0-9a-f]{32}',identity['nonce']):
        raise ProbeError('invalid reserved identity')
    return ['container','create','--pull=never','--name',identity['name'],
        *[arg for key,value in labels(identity).items() for arg in ('--label',key+'='+value)],
        '--network=none','--read-only','--user=1000:1000','--workdir=/',
        '--cap-drop=ALL','--security-opt=no-new-privileges','--pids-limit=64',
        '--memory='+str(MEMORY),'--memory-swap='+str(MEMORY),'--cpus=1','--cpuset-cpus='+str(cpu),
        '--cgroupns=private','--ipc=private','--restart=no','--entrypoint=/bin/sh',identity['imageId'],*COMMAND]


class ReserveMonitor:
    """Independent bounded sampling, not proof of inter-sample headroom.

    Holds PID-derived visible ancestor FDs. A recorded breach/drift/read failure
    aborts foreground commands and enters cleanup. Cleanup keeps the collector
    running but is not prevented by a breach. A removed pinned worker group is
    recorded, not confused with an arbitrary missing resource file.
    """
    def __init__(self):
        self.lock=threading.RLock();self.entries=[];self.samples=[];self.failure=None
        self.done=threading.Event();self.thread=None;self.minimum=None
        observation=resources.observe();self.initial=observation
        root=resources._directory('/sys/fs/cgroup');chain=[]
        try:
            chain=resources.locate(root,os.getpid())
            if len(chain)!=len(observation['ancestors']): raise ProbeError('outer hierarchy changed')
            for (path,fd),row in zip(chain,observation['ancestors']):
                if path!=row['path'] or resources._identity(fd)!=row['identity']: raise ProbeError('outer identity changed')
                self.add(path,fd,False)
            self.sample();self.check()
        except BaseException:
            self.stop();raise
        finally:
            for _,fd in chain:os.close(fd)
            os.close(root)
        self.thread=threading.Thread(target=self.collect,name='h127-reserve-monitor',daemon=True)
        self.thread.start()

    def add(self,path,fd,worker):
        with self.lock:
            identity=resources._identity(fd);constraints=resources.constraints(fd)
            duplicate=os.dup(fd)
            try:self.entries.append({'path':path,'fd':duplicate,'identity':identity,
                'constraints':constraints,'worker':worker,'removed':False})
            except BaseException:os.close(duplicate);raise

    def sample(self):
        with self.lock:
            if len(self.samples)>=1024: raise ProbeError('reserve monitor sample bound reached')
            rows=[];available=[]
            for entry in self.entries:
                fd=entry['fd']
                if entry['removed']:continue
                if os.fstat(fd).st_nlink==0 and entry['worker']:
                    entry['removed']=True;rows.append({'path':entry['path'],'removedPinnedGroup':entry['identity']});continue
                constraints=resources.constraints(fd)
                if constraints!=entry['constraints'] or resources._identity(fd)!=entry['identity']:
                    raise ProbeError('monitored kernel constraints or identity changed')
                current=resources.number(resources._read(fd,'memory.current'))
                maximum=constraints['memoryMaxBytes']
                row={'path':entry['path'],'identity':entry['identity'],'memoryCurrentBytes':current,'memoryMaxBytes':maximum}
                if maximum is not None and not entry['worker']:
                    row['availableBytes']=maximum-current;available.append(maximum-current)
                rows.append(row)
            self.samples.append({'monotonicNs':time.monotonic_ns(),'groups':rows})
            if not available: raise ProbeError('no finite outer reserve observation')
            value=min(available);self.minimum=value if self.minimum is None else min(self.minimum,value)
            if value<RESERVE: raise ProbeError('observed outer reserve breached')

    def collect(self):
        while not self.done.wait(0.05):
            try:self.sample()
            except BaseException as e:
                with self.lock:self.failure=self.failure or str(e)
                # Keep sampling through cleanup; the first failure remains fatal.

    def check(self):
        with self.lock:
            if self.failure is not None:raise ProbeError(self.failure)

    def finish(self):
        # Freeze collection, then sample and check before any positive journal
        # state. A late collector failure cannot be hidden by finalization.
        self.done.set()
        if self.thread is not None:self.thread.join()
        try:self.sample()
        except BaseException as e:
            with self.lock:self.failure=self.failure or str(e)
        self.check()

    def stop(self):
        self.done.set()
        if self.thread is not None:self.thread.join()
        with self.lock:
            for entry in self.entries:
                if entry['fd'] is not None:os.close(entry['fd']);entry['fd']=None

    def summary(self):
        with self.lock:return {'intervalSeconds':0.05,'minimumObservedOuterReserveBytes':self.minimum,
            'requiredOuterReserveBytes':RESERVE,'failure':self.failure,'samples':self.samples,
            'initialObservation':self.initial,
            'boundary':'Visible pinned groups and bounded sampling only; hidden ancestors and between-sample pressure are not authenticated.'}


class PinnedGroup:
    def __init__(self,pid,container,cpu):
        self.chain = []
        self.observation = resources.observe(pid)
        root = resources._directory('/sys/fs/cgroup')
        try: self.chain = resources.locate(root,pid)
        finally: os.close(root)
        try:
            leaf = self.observation['ancestors'][-1]
            path,fd = self.chain[-1]
            if len(self.chain)<2 or path!=leaf['path'] or resources._identity(fd)!=leaf['identity']:
                raise ProbeError('cgroup identity changed before pinning')
            if path.rsplit('/',1)[-1] not in (container,'docker-'+container+'.scope'):
                raise ProbeError('PID-derived cgroup does not identify owned container')
            c = resources.constraints(fd)
            if (c['memoryMaxBytes'],c['swapMaxBytes'],c['cpuMax'],c['effectiveCpuIntervals']) != (MEMORY,0,{'quota':100000,'period':100000},[[cpu,cpu]]):
                raise ProbeError('actual kernel probe limits differ')
            proc = resources._directory('/proc/'+str(pid))
            try:
                if resources._process(proc,pid)!=self.observation['process']:
                    raise ProbeError('process identity changed before cgroup pinning')
            finally: os.close(proc)
            self.before = {'path':path,'identity':resources._identity(fd),
                'memoryEvents':resources.counters(resources._read(fd,'memory.events'),['oom','oom_kill'])}
        except BaseException:
            self.close();raise

    def close(self):
        for _,fd in self.chain: os.close(fd)
        self.chain=[]

    def removed(self):
        path,fd = self.chain[-1]; parent=self.chain[-2][1]
        try: entry=os.stat(path.rsplit('/',1)[-1],dir_fd=parent,follow_symlinks=False)
        except FileNotFoundError: entry=None
        current=os.fstat(fd)
        if entry is None and current.st_nlink==0:
            return {'removed':True,'pinnedIdentity':resources._identity(fd),'links':0,'parentEntryAbsent':True}
        if entry is not None and (entry.st_dev,entry.st_ino)!=(current.st_dev,current.st_ino):
            raise ProbeError('cgroup path reused/replaced')
        return {'removed':False,'pinnedIdentity':resources._identity(fd),
                'pinnedLinks':current.st_nlink,'parentEntryAbsent':entry is None}


def cleanup(client, identity, container, pinned, timeout=10):
    """Destructive operations target only a full ID rechecked for nonce ownership.

    A daemon failure or missing pin is not absence/drain evidence. The journal
    remains active even after this returns an observation.
    """
    client.guard=None  # reserve failure triggers cleanup, never suppresses it
    started=time.monotonic_ns();deadline=started+timeout*10**9
    client.deadline=deadline  # one deadline includes info/inspect/kill/rm/list calls
    data=ownership(client.inspect(container),identity,container)
    if data['State']['Running']:
        ownership(client.inspect(container),identity,container)
        client.call(['container','kill','--signal=KILL',container])
    while True:
        data=ownership(client.inspect(container),identity,container)
        state=data['State']
        if type(state['Running']) is not bool or type(state['Pid']) is not int or type(state['Restarting']) is not bool:
            raise ProbeError('malformed container state')
        if not state['Running'] and state['Pid']==0 and not state['Restarting']: break
        if time.monotonic_ns()>=deadline: raise ProbeError('container stop unresolved')
        time.sleep(0.02)
    exit_info={key:data['State'][key] for key in ('ExitCode','OOMKilled','Status')}
    ownership(client.inspect(container),identity,container)
    client.call(['container','rm',container])  # no --force or name-based mutation
    if client.listed('id='+container) or client.listed('name=^/'+identity['name']+'$'):
        raise ProbeError('owned Docker identity persists after removal')
    if pinned is None: raise ProbeError('Docker removed; kernel drain pin unavailable')
    while True:
        removal=pinned.removed()
        completed=time.monotonic_ns()
        if completed>=deadline: raise ProbeError('cleanup global deadline expired',{'lastKernelObservation':removal})
        if removal['removed']: return {'dockerIdAbsent':True,'dockerNameAbsent':True,'kernel':removal,'exit':exit_info,
            'startedMonotonicNs':started,'completedMonotonicNs':completed,'deadlineMonotonicNs':deadline}
        if time.monotonic_ns()>=deadline: raise ProbeError('pinned cgroup removal unresolved')
        time.sleep(0.02)


def reconcile(client,identity,timeout=10):
    """Attempt full-ID recovery for an ambiguous create, never infer absence.

    Creation may still complete after an empty query. No result here releases
    the barrier; discovery only permits ownership-checked cleanup of that ID.
    """
    client.guard=None;client.deadline=time.monotonic_ns()+timeout*10**9
    rows=client.listed('name=^/'+identity['name']+'$')
    if len(rows)!=1: raise ProbeError('create reconciliation unresolved; no unique acknowledged ID')
    ownership(client.inspect(rows[0]),identity,rows[0])
    return rows[0]


def persist(path,value):
    with path.open('xb') as f:
        os.fchmod(f.fileno(),0o600);f.write(journal_module.encode(value));f.flush();os.fsync(f.fileno())
    fd=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY)
    try: os.fsync(fd)
    finally: os.close(fd)


def probe(destination,image):
    destination=Path(destination)
    if destination.parent!=destination.parent.resolve(strict=True): raise ProbeError('noncanonical probe parent')
    image_id(image)
    destination.mkdir(mode=0o700)
    store=destination/'state';store.mkdir(mode=0o700)
    locator=journal_module.provision(store);persist(destination/'locator.json',locator)
    source_paths=[Path(__file__),*[Path(__file__).with_name(name+'.py') for name in ('lifecycle-journal','kernel-resources','measurement-clock')]]
    source_pins={p.name:digest_file(p) for p in source_paths}
    result={'recipe':RECIPE,'measurementAccepted':False,'postCreateBarrierReleased':False,
            'sourcePins':source_pins,'clockStart':clock.capture()}
    old={}
    def interrupted(number,frame): raise ProbeError('controller interrupted by signal '+str(number))
    for number in (signal.SIGINT,signal.SIGTERM,signal.SIGHUP): old[number]=signal.signal(number,interrupted)
    pinned=client=monitor=None;container=None;identity=None;error=None
    try:
        with journal_module.Journal(store,locator) as journal:
            monitor=ReserveMonitor()
            client=Docker();client.guard=monitor.check
            client.deadline=time.monotonic_ns()+45*10**9  # probe orchestration only, not a proof budget
            cpu=min(os.sched_getaffinity(0))
            plan=journal_module.digest({'recipe':RECIPE,'image':image,'cpu':cpu})
            identity=journal.reserve(plan,image);result['identity']=identity
            try:
                if client.listed('name=^/'+identity['name']+'$'): raise ProbeError('reserved name already exists')
                journal.advance('create-intent',{})
                raw=client.call(create_args(identity,cpu));container=exact_hex(raw.decode('ascii').strip())
                journal.advance('created',{'containerId':container})
                policy(client.inspect(container),identity,container,cpu)
                journal.advance('start-intent',{})
                client.call(['container','start',container])
                journal.advance('started',{'containerId':container})
                data=ownership(client.inspect(container),identity,container)
                policy(data,identity,container,cpu)
                if not data['State']['Running'] or type(data['State']['Pid']) is not int or data['State']['Pid']<=0:
                    raise ProbeError('probe PID not running')
                pinned=PinnedGroup(data['State']['Pid'],container,cpu)
                monitor.add(pinned.before['path'],pinned.chain[-1][1],True)
                monitor.check()
                result['kernelObservation']=pinned.observation
                journal.advance('kernel-observed',{'containerId':container,'cgroup':pinned.before})
            except BaseException as e: error=e
            finally:
                # First interruption initiates cleanup. Further catchable signals
                # cannot interrupt this cleanup attempt; SIGKILL retains barrier.
                for number in old: signal.signal(number,signal.SIG_IGN)
                if container is None and journal.read_active()['events'][-1]['state']=='create-intent':
                    try:
                        container=reconcile(client,identity)
                        result['reconciledContainerId']=container
                    except BaseException as e:result['reconciliationError']=str(e)
                if container is not None:
                    try: result['cleanup']=cleanup(client,identity,container,pinned)
                    except BaseException as e:
                        result['cleanupError']=str(e);result['cleanupFailureFacts']=getattr(e,'facts',{});error=error or e
                else: result['cleanupError']='No acknowledged container ID; create outcome remains unknown'
                try: monitor.finish()
                except BaseException as e: error=error or e
                active=journal.read_active();state=active['events'][-1]['state']
                if state=='create-intent': journal.advance('create-unknown',{})
                elif state=='start-intent': journal.advance('start-unknown',{})
                state=journal.read_active()['events'][-1]['state']
                if state=='kernel-observed' and 'cleanup' in result and error is None:
                    journal.advance('drain-observed',{'observationSha256':journal_module.digest(result['cleanup'])})
                    result['status']='probe-drain-observed'
                elif state in ('created','started','kernel-observed','create-unknown','start-unknown'):
                    journal.advance('cleanup-unresolved',{'reason':str(error or result.get('cleanupError'))})
                    result['status']='unresolved'
                else: result['status']='unresolved'
                result['activeBarrierState']=journal.read_active()['events'][-1]['state']
    except BaseException as e:
        error=error or e; result['status']='unresolved'
    finally:
        for number,handler in old.items(): signal.signal(number,handler)
        if monitor is not None:
            monitor.stop();result['reserveMonitor']=monitor.summary()
        if pinned is not None: pinned.close()
        if client is not None:
            result['client']={'binarySha256':client.binary,'socket':client.socket,'daemon':client.daemon,'calls':client.trace}
        try:
            result['clockEnd']=clock.capture()
            if result['clockEnd']['bootId']!=result['clockStart']['bootId'] or source_pins!={p.name:digest_file(p) for p in source_paths}:
                raise ProbeError('probe source or boot identity changed')
        except BaseException as e: error=error or e;result['status']='unresolved'
        if error is not None: result['error']=str(error)
        persist(destination/'probe.json',result)
    return result


def reserve_probe(destination):
    # One-shot diagnostic reservation under the global writer lock. Never
    # replace or remove it, even after a positive observation. A new destination
    # cannot bypass a prior unresolved post-create journal.
    persist(RESERVATION,{'recipe':RECIPE,'destination':str(Path(destination).absolute()),
                         'bootId':clock.boot_id(),'postCreateBarrierReleased':False})


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('destination',type=Path);p.add_argument('image')
    a=p.parse_args()
    with open(LOCK,'a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        reserve_probe(a.destination)
        result=probe(a.destination,a.image)
    print(json.dumps({'status':result['status'],'measurementAccepted':False,'postCreateBarrierReleased':False}))
    return 0 if result['status']=='probe-drain-observed' else 2


if __name__=='__main__': raise SystemExit(main())
