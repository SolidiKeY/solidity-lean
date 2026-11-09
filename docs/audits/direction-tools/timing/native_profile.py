#!/usr/bin/env python3
"""Linux/x86-64 statistical user-IP sampling, Python stdlib only.
Requires --cloud-vm and runs one immutable module under measure.py resource guards.
python3 .../native_profile.py --cloud-vm --repo DIR --file PATH --work NEWDIR
Counts are statistical CPU samples, not exact times, allocations, or wall partitions.
"""
import argparse,bisect,collections,ctypes,fcntl,hashlib,importlib.util,json,mmap,os,pathlib,platform,re,resource,struct,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent
class Attr(ctypes.Structure):
    _fields_=[('type',ctypes.c_uint32),('size',ctypes.c_uint32),('config',ctypes.c_uint64),('period',ctypes.c_uint64),('sample_type',ctypes.c_uint64),('read_format',ctypes.c_uint64),('flags',ctypes.c_uint64),('wakeup',ctypes.c_uint32),('bp_type',ctypes.c_uint32),('config1',ctypes.c_uint64),('config2',ctypes.c_uint64),('branch',ctypes.c_uint64),('regs',ctypes.c_uint64),('stack',ctypes.c_uint32),('clockid',ctypes.c_int32)]
class Sampler:
    def __init__(self):
        self.events={};self.maps=[];self.pid=None;self.counts=collections.Counter();self.lost=0;self.frequency=99;self.libc=ctypes.CDLL(None,use_errno=True);self.started=time.monotonic()
    def poll(self,group):
        # Only compiler processes in the fresh session created by our meter.
        for entry in pathlib.Path('/proc').iterdir():
            if not entry.name.isdigit(): continue
            try:
                if os.getpgid(int(entry.name))!=group: continue
                status=(entry/'status').read_text()
                if not re.search(r'^Name:\s+lean$',status,re.M) or re.search(r'^State:\s+Z',status,re.M): continue
                pid=int(entry.name)
                if self.pid is not None and self.pid!=pid: raise RuntimeError('more than one Lean PID observed; mixed-ASLR profile rejected')
                self.pid=pid
                executable=[line for line in (entry/'maps').read_text().splitlines() if 'x' in line.split()[1]]
                self.maps=list(dict.fromkeys(self.maps+executable))
                for task in (entry/'task').iterdir():
                    tid=int(task.name)
                    if tid in self.events: continue
                    attr=Attr(type=1,size=ctypes.sizeof(Attr),config=1,period=self.frequency,sample_type=1,flags=1|(1<<5)|(1<<6)|(1<<10),wakeup=1)
                    fd=self.libc.syscall(298,ctypes.byref(attr),tid,-1,-1,0)
                    if fd<0:
                        error=ctypes.get_errno()
                        if error==3: continue
                        raise OSError(error,os.strerror(error))
                    try:
                        buf=mmap.mmap(fd,65*mmap.PAGESIZE,flags=mmap.MAP_SHARED,prot=mmap.PROT_READ|mmap.PROT_WRITE)
                        fcntl.ioctl(fd,0x2400,0)
                    except BaseException: os.close(fd);raise
                    self.events[tid]=[fd,buf,0]
            except (FileNotFoundError,ProcessLookupError): continue
        self.drain()
    def drain(self):
        for event in self.events.values():
            fd,buf,tail=event;head=struct.unpack_from('<Q',buf,1024)[0];offset,size=struct.unpack_from('<QQ',buf,1040)
            if not offset or not size: continue
            if head-tail>size: raise RuntimeError('perf ring overrun; profile unusable')
            def chunk(pos,n):
                start=pos%size;first=min(n,size-start)
                return buf[offset+start:offset+start+first]+buf[offset:offset+n-first]
            while tail<head:
                kind,misc,length=struct.unpack('<IHH',chunk(tail,8))
                if length<8 or tail+length>head: raise RuntimeError('incomplete perf record')
                data=chunk(tail+8,length-8)
                if kind==9: self.counts[struct.unpack_from('<Q',data)[0]]+=1
                elif kind==2: self.lost+=struct.unpack_from('<Q',data,8)[0]
                tail+=length
            event[2]=tail;struct.pack_into('<Q',buf,1032,tail)
    def close(self):
        try:
            for fd,buf,tail in self.events.values():
                try: fcntl.ioctl(fd,0x2401,0)
                except OSError as error:
                    if error.errno not in (3,19): raise
            self.drain()
        finally:
            for fd,buf,tail in self.events.values(): buf.close();os.close(fd)

def elf_symbols(path):
    with open(path,'rb') as handle, mmap.mmap(handle.fileno(),0,access=mmap.ACCESS_READ) as data:
        if data[:6]!=b'\x7fELF\x02\x01': return None
        phoff,shoff=struct.unpack_from('<QQ',data,32);phsize,phnum,shsize,shnum=struct.unpack_from('<HHHH',data,54)
        loads=[]
        for i in range(phnum):
            kind,flags,off,addr,physical,filesize,memsize,align=struct.unpack_from('<IIQQQQQQ',data,phoff+i*phsize)
            if kind==1: loads.append((off,off+filesize,addr))
        sections=[struct.unpack_from('<IIQQQQIIQQ',data,shoff+i*shsize) for i in range(shnum)];symbols={}
        for section in sections:
            name,kind,flags,addr,off,size,link,info,align,entrysize=section
            if kind not in (2,11) or entrysize!=24: continue
            strings=sections[link];stringbase=strings[4]
            for pos in range(off,off+size,entrysize):
                name,info,other,index,value,size=struct.unpack_from('<IBBHQQ',data,pos)
                if info&15 not in (2,10) or not index or not value or not size: continue
                end=data.find(b'\0',stringbase+name);label=data[stringbase+name:end].decode(errors='replace')
                symbols[value]=(size,label)
        starts=sorted(symbols)
        return loads,starts,symbols

def symbolize(sampler):
    mappings=[]
    for line in sampler.maps:
        cols=line.split(maxsplit=5)
        if len(cols)<6 or 'x' not in cols[1] or not cols[5].startswith('/'): continue
        start,end=(int(x,16) for x in cols[0].split('-'));mappings.append((start,end,int(cols[2],16),cols[5]))
    cache={};counts=collections.Counter();unknown=0
    for ip,count in sampler.counts.items():
        candidates=[row for row in mappings if row[0]<=ip<row[1]]
        mapping=candidates[0] if len(candidates)==1 else None
        if not mapping: unknown+=count;continue
        start,end,offset,path=mapping
        if path not in cache:
            try: cache[path]=elf_symbols(path)
            except OSError: cache[path]=None
        if cache[path] is None: unknown+=count;continue
        loads,starts,symbols=cache[path];filepos=ip-start+offset;load=next((row for row in loads if row[0]<=filepos<row[1]),None)
        if load is None: unknown+=count;continue
        address=load[2]+filepos-load[0];index=bisect.bisect_right(starts,address)-1
        if index<0: unknown+=count;continue
        base=starts[index];size,label=symbols[base]
        if address>=base+size: unknown+=count;continue
        counts[(path,label)]+=count
    total=sum(sampler.counts.values());binaries=[]
    for path in sorted(cache):
        if cache[path] is None: continue
        digest=hashlib.sha256()
        with open(path,'rb') as handle:
            for block in iter(lambda:handle.read(1024*1024),b''): digest.update(block)
        binaries.append({'path':path,'sha256':digest.hexdigest()})
    return {'method':'99Hz per-thread software task-clock user-IP samples; every observed Lean thread in owned session; OS kernel/hypervisor excluded (Lean kernel remains user-space sampled); startup/short-lived threads may be missed; no exact CPU/elapsed or allocation attribution','symbolized_binaries':binaries,'samples':total,'lost_samples':sampler.lost,'unknown_symbol_samples':unknown,'sampled_threads':len(sampler.events),'top_symbols':[{'binary':path,'symbol':label,'samples':n,'fraction_of_samples':n/total} for (path,label),n in sorted(counts.items(),key=lambda item:(-item[1],item[0]))[:40]]}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--cloud-vm',action='store_true');ap.add_argument('--repo',type=pathlib.Path,required=True);ap.add_argument('--file',required=True);ap.add_argument('--expected-head',choices=['d6fd95f0886775d7c286813fa9b993a40ba7a777','047f63070309f436b66c61e276ab3b6d1169265a','6ef2e7eda01080e5d5fd7474354c1a71adab5071'],default='d6fd95f0886775d7c286813fa9b993a40ba7a777');ap.add_argument('--auto-implicit-false',action='store_true');ap.add_argument('--work',type=pathlib.Path,required=True);args=ap.parse_args()
    if not args.cloud_vm: ap.error('explicit --cloud-vm required; host execution unsupported')
    if platform.system()!='Linux' or platform.machine()!='x86_64': ap.error('Linux/x86-64 required')
    repo=args.repo.resolve();file=pathlib.Path(args.file)
    if file.is_absolute() or '..' in file.parts: ap.error('relative module path required')
    head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
    assert not subprocess.check_output(['git','-C',str(repo),'status','--porcelain','--untracked-files=no'],text=True).strip()
    assert head==args.expected_head, 'unfrozen measurement head'
    assert file.suffix=='.lean' and not (repo/file).is_symlink() and repo in (repo/file).resolve().parents
    subprocess.check_output(['git','-C',str(repo),'ls-files','--error-unmatch','--',args.file])
    spec=importlib.util.spec_from_file_location('meter',HERE/'measure.py');meter=importlib.util.module_from_spec(spec);spec.loader.exec_module(meter);meter.CLOUD_VM_OPT_IN=True
    if meter.active_compilers(): raise RuntimeError('another compiler is active; refusing launch')
    versions={name:subprocess.check_output([name,'--version'],cwd=repo,text=True).strip() for name in ('lean','lake')}
    work=args.work.resolve()
    if work==repo or repo in work.parents or work==HERE.parents[3] or HERE.parents[3] in work.parents: ap.error('--work must be outside checkouts')
    work.mkdir(parents=True,exist_ok=False);sampler=Sampler()
    command=['lake','env','lean','-j1','--tstack=131072']+(['-DautoImplicit=false'] if args.auto_implicit_false else [])+[args.file]
    before=resource.getrusage(resource.RUSAGE_CHILDREN)
    try: result=meter.command(command,repo,work/'lean.log',600,observer=sampler)
    finally: sampler.close()
    raw={'head':head,'lean_pid':sampler.pid,'frequency_hz':sampler.frequency,'sampled_threads':len(sampler.events),'lost_samples':sampler.lost,'maps':sampler.maps,'ip_counts':sorted(sampler.counts.items())}
    meter.atomic_write_json(work/'native-samples.json',raw)
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    usage={name:getattr(after,name)-getattr(before,name) for name in ('ru_utime','ru_stime','ru_majflt','ru_minflt','ru_inblock','ru_oublock','ru_nvcsw','ru_nivcsw')}
    profile=symbolize(sampler);meter.atomic_write_json(work/'native-profile.json',{'head':head,'versions':versions,'environment':meter.capture_environment(repo),'check':result,'child_rusage_delta':usage,'rusage_boundary':'awaited Lake invocation plus descendants; sampler IPs cover Lean user-space only','profile':profile})
    if result['exit_code'] or not profile['samples'] or profile['lost_samples']: raise SystemExit('failed or incomplete native profile')
    print('PASS',profile['samples'],'samples;',profile['unknown_symbol_samples'],'unknown symbols')
if __name__=='__main__': main()
