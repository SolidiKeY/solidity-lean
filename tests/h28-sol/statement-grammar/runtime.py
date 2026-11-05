#!/usr/bin/env python3
"""One recorded serial H28 check in the task-owned 12 GiB/no-swap container.
External tool setup is captured and checked, never silently downloaded here.
Build accepts a module only when all local imports already have artifacts;
this prevents a dependency fan-out of fresh Lean compiler processes.
"""
import fcntl, hashlib, json, os, pathlib, re, signal, subprocess, sys, time, tomllib
ROOT = pathlib.Path(__file__).resolve().parents[3]
TOOLS = pathlib.Path('/workspace/h28-tools')
CONTAINER = 'h28-statement-runtime'
CID = 'ccdfcdecd8f9fe2d854a86d019fdc69d9d242e411a2fb97750e6e7ef7185b93c'
EVIDENCE = pathlib.Path('/workspace/h28-statement-grammar-evidence')
LIMIT, RESERVE = 12 * 1024**3, 4 * 1024**3

def command(args, **kw):
    return subprocess.run(args,cwd=ROOT,text=True,capture_output=True,timeout=30,**kw)

def available():
    cap=int(pathlib.Path('/sys/fs/cgroup/memory.max').read_text())
    used=int(pathlib.Path('/sys/fs/cgroup/memory.current').read_text())
    mem=next(int(s.split()[1])*1024 for s in pathlib.Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:'))
    return min(cap-used,mem)

def interrupted(signum,frame):
    raise RuntimeError('interrupted by signal '+str(signum))

def main():
    if len(sys.argv)!=3 or sys.argv[1] not in ('build','diag','gate','solc'):
        raise SystemExit('usage: runtime.py build MODULE | diag FILE | gate FILE | solc RUNNER')
    mode,target=sys.argv[1:]
    EVIDENCE.mkdir(exist_ok=True)
    out=EVIDENCE/('run-'+str(time.time_ns()));out.mkdir()
    record={'mode':mode,'target':target,'status':'fail','exit':None}
    proc=None;owned=False;locked=False;lock=None;samples=[];start=time.monotonic()
    for sig in [signal.SIGTERM,signal.SIGINT]:signal.signal(sig,interrupted)
    try:
        lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a')
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);locked=True
        record['head']=command(['git','rev-parse','HEAD'],check=True).stdout.strip()
        assert available()>=RESERVE,'insufficient VM headroom'
        j=json.loads(command(['docker','inspect',CONTAINER],check=True).stdout)[0]
        assert j['Id']==CID,'not the owned task runtime'
        owned=True
        assert j['HostConfig']['Memory']==LIMIT and j['HostConfig']['MemorySwap']==LIMIT
        assert j['HostConfig']['NanoCpus']==10**9 and j['State']['Running']
        assert 'LEAN_NUM_THREADS=1' in j['Config']['Env']
        record.update(container_id=CID,memory=LIMIT,swap=0,lean_num_threads=1)
        command(['scripts/coord-tools/lean-mcp','stop'],check=True)
        config=tomllib.loads((TOOLS/'lakefile.toml').read_text())
        assert config['srcDir']==str(ROOT) and config['buildDir']==str(ROOT/'.lake/build')
        assert '-j1' in next(lib for lib in config['lean_lib'] if lib['name']=='Solidity')['weakLeanArgs']
        wrapper=(TOOLS/'bin/lake').read_text()
        assert 'env lean -j1' in wrapper and '"$@" -j1 --tstack=131072' in wrapper
        assert '-j1 "$@"' in (TOOLS/'bin/lean').read_text()
        assert 'LEAN_LSP_MAX_OPEN_FILES=4' in (TOOLS/'mcp-server').read_text()
        (out/'tools').mkdir()
        for name in ['lakefile.toml','bin/lake','bin/lean','mcp-server']:
            dest=out/'tools'/name;dest.parent.mkdir(exist_ok=True,parents=True)
            dest.write_bytes((TOOLS/name).read_bytes())
        record['explicit_lean_j1']='verified external config and wrapper; copies in tools/'
        src=ROOT/(target.replace('.','/')+'.lean') if mode=='build' else ROOT/target
        assert src.is_file(),'target must be a local source file/module'
        if mode=='build':
            assert target.startswith('Solidity.') and re.fullmatch(r'[A-Za-z0-9_.]+',target)
            preflight=command(['docker','exec','--user','1000:1000',CONTAINER,'lake','-f',str(TOOLS/'lakefile.toml'),'--no-build','build',target+':deps'])
            (out/'dependencies.log').write_text(preflight.stdout+preflight.stderr)
            assert preflight.returncode==0,'dependencies must already be current; prebuild each serially'
        if mode=='build':
            for dep in re.findall(r'^import ([A-Za-z0-9_.]+)',src.read_text(),re.M):
                local=ROOT/(dep.replace('.','/')+'.lean')
                if local.exists():
                    assert (ROOT/'.lake/build/lib/lean'/(dep.replace('.','/')+'.olean')).is_file(), 'prebuild import serially: '+dep
        inputs=list((ROOT/'Solidity/Frontend/StatementGrammarH28').rglob('*'))+list((ROOT/'tests/h28-sol/statement-grammar').rglob('*'))+[ROOT/'Solidity/Source/Syntax.lean',ROOT/'docs/feature-work/h28-statement-grammar.md']+list(ROOT.glob('Solidity/Frontend/Checked/*.lean'))+list(ROOT.glob('tests/upstream/grammar-0.8.38/*.g4'))
        (out/'inputs.json').write_text(json.dumps({str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs if p.is_file()},indent=2))
        if mode=='solc':assert target in ('tests/h28-sol/statement-grammar/solc-fixtures.mjs','tests/h28-sol/statement-grammar/contextual-revert-solc.mjs')
        if mode=='diag':cmd=['scripts/coord-tools/lean-mcp','diag',target]
        else:
            inner=['lake','-f',str(TOOLS/'lakefile.toml'),'build',target] if mode=='build' else ['bash','scripts/coord-tools/gate.sh','per-file',target]
            if mode=='solc':inner=['/workspace/h28-tools/node','--max-old-space-size=1024',target,'/workspace/h28-tools/soljson-v0.8.38+commit.1835d247.js',str(out/'solc-results')]
            cmd=['docker','exec','--user','1000:1000','-e','PATH=/workspace/h28-tools/bin:/workspace/h28-tools/lean-4.24.0-linux/bin:/usr/bin:/bin','-e','GATE_LOGS='+str(out/'gates'),CONTAINER,'/usr/bin/time','-v']+inner
        record['command']=cmd
        env=dict(os.environ,LEAN_MCP_SERVER_CMD='docker exec -i --user 1000:1000 h28-statement-runtime /workspace/h28-tools/mcp-server')
        with (out/'output.log').open('w') as log:
            proc=subprocess.Popen(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,env=env)
            while proc.poll() is None:
                assert available()>=RESERVE,'VM headroom guard'
                assert time.monotonic()-start<600,'600 second wall guard'
                top=command(['docker','top',CONTAINER,'-eo','pid,stat,comm,args'],check=True).stdout
                samples.append(top)
                lean=[s for s in top.splitlines()[1:] if len(s.split())>2 and s.split()[2]=='lean' and not s.split()[1].startswith('Z')]
                assert all('-j1' in s for s in lean),'observed Lean without explicit -j1'
                assert len([s for s in lean if '--server' not in s])<=1,'observed concurrent Lean workers'
                time.sleep(.25)
        (out/'process-samples.json').write_text(json.dumps(samples,indent=2))
        record['exit']=proc.returncode
        assert proc.returncode==0,'gate command failed'
        record['status']='pass'
    except BaseException as ex:
        record.update(status='fail',error=str(ex))
    finally:
        try:
            (out/'process-samples.json').write_text(json.dumps(samples,indent=2))
            if locked:
                command(['scripts/coord-tools/lean-mcp','stop'],check=True)
            if owned:
                cgroup=command(['docker','exec',CONTAINER,'sh','-c','cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max /sys/fs/cgroup/memory.peak /sys/fs/cgroup/memory.events'],check=True).stdout
                record['container_lifetime_cgroup']=cgroup
                lines=cgroup.splitlines();assert lines[:2]==[str(LIMIT),'0']
                events=dict(s.split() for s in lines[3:])
                assert int(events['oom'])==0 and int(events['oom_kill'])==0,'OOM evidence'
        except BaseException as ex:
            record.update(status='fail',cleanup_or_resource_error=str(ex))
        if owned and record['status']!='pass':
            # Docker clients can exit before their server-side children. A
            # failed check always stops the exact owned runtime, even then.
            try:
                current=json.loads(command(['docker','inspect',CID],check=True).stdout)[0]
                assert current['Id']==CID
                if current['State']['Running']:
                    command(['docker','kill',CID],check=True)
                if proc is not None and proc.poll() is None:proc.wait(timeout=10)
                record['failure_runtime_stopped']=True
            except BaseException as ex:
                record['failure_runtime_stopped']=False
                record['failure_stop_error']=str(ex)
            try:command(['scripts/coord-tools/lean-mcp','stop'],check=True)
            except BaseException as ex:record['failure_daemon_cleanup_error']=str(ex)
        record['seconds']=time.monotonic()-start
        (out/'result.json').write_text(json.dumps(record,indent=2))
        (out/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(out))+'\n' for p in sorted(out.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'))
    print(json.dumps({'status':record['status'],'exit':record['exit'],'evidence':str(out)}))
    return 0 if record['status']=='pass' else 1
if __name__=='__main__':sys.exit(main())
