#!/usr/bin/env python3
"""Serial, cold project-artifact Lane build. No shared artifact cache.
Usage: measure.py TOOLCHAIN_DIR EVIDENCE_RUN_DIR [--key-only | --modules NAME... | --check-file FILE --lean-path DIR]
Each run must use a new output directory. OS page cache is deliberately warm
and uncontrolled in BOTH runs; cold means no project artifacts, not drop_caches.
"""
import json, os, pathlib, resource, signal, subprocess, sys, time
root=pathlib.Path(__file__).resolve().parents[4]
tool=pathlib.Path(sys.argv[1]).resolve(); out=pathlib.Path(sys.argv[2]).resolve()
out.mkdir(parents=True,exist_ok=False)
env=os.environ.copy(); env.update(PATH=str(tool/'bin')+':'+env['PATH'],LEAN_NUM_THREADS='1',XDG_CACHE_HOME=str(out/'cache'))
config=out/'lane.toml'
config.write_text('name = "solidity-lean"\nversion = "0.1.0"\nenableArtifactCache = false\nbuildDir = '+json.dumps(str(out/'build'))+'\n[[lean_lib]]\nname = "Solidity"\nweakLeanArgs = ["--tstack=131072", "-j1", "-M8192"]\n')
records=[]
if int(pathlib.Path('/sys/fs/cgroup/memory.swap.current').read_text()) != 0 or len(pathlib.Path('/proc/swaps').read_text().splitlines()) != 1:
    raise RuntimeError('RESOURCE_SWAP: swap must be absent')
(out/'resources.json').write_text(json.dumps({k:pathlib.Path('/sys/fs/cgroup',k).read_text().strip() for k in ['memory.max','memory.current','memory.swap.max','memory.swap.current','cpu.max']},indent=2))
(out/'harness.sha256').write_text(__import__('hashlib').sha256(pathlib.Path(__file__).read_bytes()).hexdigest()+'\n')
def available():
    host=int(next(l.split()[1] for l in pathlib.Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')))*1024
    cg=pathlib.Path('/sys/fs/cgroup')
    limit=(cg/'memory.max').read_text().strip()
    return min(host,int(limit)-int((cg/'memory.current').read_text())) if limit!='max' else host
def run(cmd,label):
    if available()<4*1024**3: raise RuntimeError('RESOURCE_RESERVE: less than 4GiB available')
    start=time.monotonic(); peak=0; stopped=None
    with (out/(label+'.log')).open('w') as log:
        p=subprocess.Popen(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        while p.poll() is None:
            rss=0
            for d in pathlib.Path('/proc').iterdir():
                if not d.name.isdigit(): continue
                try:
                    # Every descendant inherits our dedicated process group.
                    if os.getpgid(int(d.name))==p.pid:
                        rss+=int(next(l.split()[1] for l in (d/'status').read_text().splitlines() if l.startswith('VmRSS:')))*1024
                except (OSError,StopIteration,ProcessLookupError): pass
            peak=max(peak,rss)
            if rss>12*1024**3 or available()<4*1024**3:
                stopped='RESOURCE_STOP'; os.killpg(p.pid,signal.SIGTERM); p.wait(); break
            time.sleep(.1)
        rc=p.wait()
    rec=dict(command=cmd,label=label,exit=rc,wall_seconds=time.monotonic()-start,peak_sampled_aggregate_rss_bytes=peak,stop=stopped)
    records.append(rec); (out/'results.json').write_text(json.dumps(records,indent=2)+'\n'); print(json.dumps(rec),flush=True)
    return rc==0 and not stopped
for binary in ['lean','lake']:
    if not run([str(tool/'bin'/binary),'--version'],binary+'-version'): sys.exit(2)
if not run([str(tool/'bin'/'lake'),'-f',str(config),'--no-cache','build','Solidity.KeySort:olean'],'keysort'): sys.exit(3)
if '--key-only' in sys.argv: sys.exit(0)
if '--full-gate' in sys.argv or '--serial-targets' in sys.argv:
    # Use the official binaries and libraries unchanged. A private launch wrapper
    # serializes compiler invocations; it is not a different Lean build.
    sysroot=out/'serial-sysroot'; (sysroot/'bin').mkdir(parents=True)
    for item in tool.iterdir():
        if item.name!='bin': (sysroot/item.name).symlink_to(item,target_is_directory=item.is_dir())
    for item in (tool/'bin').iterdir():
        if item.name!='lean': (sysroot/'bin'/item.name).symlink_to(item)
    import shlex
    wrapper=sysroot/'bin/lean'
    wrapper.write_text('#!/bin/bash\nexec flock -x '+shlex.quote(str(out/'compiler.lock'))+' '+shlex.quote(str(tool/'bin/lean'))+' --tstack=131072 -j1 -M8192 "$@"\n')
    wrapper.chmod(0o755)
    text=(root/'lakefile.toml').read_text().replace('enableArtifactCache = true','enableArtifactCache = false')
    text=text.replace('version = "0.1.0"','version = "0.1.0"\nbuildDir = '+json.dumps(str(out/'build')))
    text=text.replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1", "-M8192"]')
    config.write_text(text)
    shims=out/'shims'; shims.mkdir()
    shim=shims/'lake'
    shim.write_text('#!/bin/bash\nexec '+shlex.quote(str(tool/'bin/lake'))+' -f '+shlex.quote(str(config))+' --no-cache "$@"\n')
    shim.chmod(0o755)
    env.update(PATH=str(shims)+':'+env['PATH'],LEAN_SYSROOT=str(sysroot),LAKE_OVERRIDE_LEAN='true')
    if '--serial-targets' in sys.argv:
        targets=sys.argv[sys.argv.index('--serial-targets')+1:]
        failed=False
        for target in targets:
            failed=not run([str(tool/'bin/lake'),'-f',str(config),'--no-cache','build',target+':olean'],target.replace('.','_')) or failed
        sys.exit(6 if failed else 0)
    sys.exit(0 if run(['bash','./run-lean.sh'],'run-lean') else 6)
if '--check-file' in sys.argv:
    filename=sys.argv[sys.argv.index('--check-file')+1]
    if '--lean-path' in sys.argv: env['LEAN_PATH']=sys.argv[sys.argv.index('--lean-path')+1]
    sys.exit(0 if run([str(tool/'bin'/'lean'),'--tstack=131072','-j1','-M8192',filename],'fixture') else 5)
# One invocation per module guarantees serial jobs even across independent branches.
modules = ['FixedPoint','FixedPoint.Laws','FixedPoint.Abi','FixedPoint.Literals','FixedPoint.Storage','FixedPoint.Conformance','Features','FeatureInfo']
if '--modules' in sys.argv: modules=sys.argv[sys.argv.index('--modules')+1:]
for module in modules:
    if not run([str(tool/'bin'/'lake'),'-f',str(config),'--no-cache','build','Solidity.Language.'+module+':olean'],module): sys.exit(4)
