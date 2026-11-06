#!/usr/bin/env python3
"""Read-only G01 namespace census; no G49 theorem/progress claim."""
import argparse
from collections import Counter
import fcntl
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time
from verify import available, sha, BASE, ROOT, SCOPE

if not __debug__:
    raise RuntimeError('H62 verification cannot run with Python optimization enabled')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ('lean-bin','pin','archive','evidence'):
        parser.add_argument('--'+arg,type=Path,required=True)
    args = parser.parse_args()
    evidence = args.evidence.resolve()
    assert not evidence.is_relative_to(ROOT), 'evidence must be off git'
    pin = json.loads(args.pin.read_text())
    assert sha(args.archive) == pin['sha256'], 'pinned archive checksum mismatch'
    assert not int(next(l for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('SwapTotal:')).split()[1]), 'swap must be disabled'
    with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],cwd=ROOT), 'census requires committed clean sources'
        head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
        evidence.mkdir(parents=True,exist_ok=True)
        build = evidence/'build'
        env = dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(build),H62_GRAPH_OUTPUT_DIR=str(evidence))
        lean = str(args.lean_bin.resolve()/'lean')
        version = subprocess.check_output([lean,'--version'],text=True)
        assert pin['toolchain'].split(':')[-1].lstrip('v') in version, 'wrong Lean'
        # Exact read-only dependencies inspected in the pinned source tree.
        modules = [Path('Solidity/Hash/CollisionBound.lean'),Path('Solidity/Keccak.lean'),
                   Path('Solidity/Roadmap/Evm.lean'),Path('Solidity/Roadmap/Contracts.lean'),SCOPE/'Exporter.lean']
        logs = []
        def run(src,output=None):
            assert available() >= 4*1024**3, '4GiB reserve missing'
            cmd = [lean,'-j1','--tstack=131072']
            if output is not None:
                output.parent.mkdir(parents=True,exist_ok=True)
                cmd += ['-o',str(output)]
            cmd += [str(src)]
            started = time.monotonic()
            logfile = evidence/(src.stem+'.log')
            def bound():
                resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
            with logfile.open('w') as out:
                proc = subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=bound)
                try:
                    while proc.poll() is None:
                        if available() < 4*1024**3 or time.monotonic()-started > 300:
                            raise RuntimeError('resource or 300s module limit crossed')
                        time.sleep(.05)
                except BaseException:
                    os.killpg(proc.pid,signal.SIGKILL)
                    proc.wait()
                    raise
            logs.append(dict(command=cmd,exit=proc.returncode,seconds=time.monotonic()-started,log=str(logfile)))
            (evidence/'commands.json').write_text(json.dumps(logs,indent=2)+'\n')
            assert proc.returncode == 0, logs[-1]
        for src in modules:
            run(src,build/src.with_suffix('.olean'))
        run(SCOPE/'Census.lean')
        assert (evidence/'roadmap-census.json').read_bytes() == (evidence/'roadmap-census-repeat.json').read_bytes(), 'census nondeterminism'
        snapshot = json.loads((evidence/'roadmap-census.json').read_text())
        rows = snapshot['declarations']
        summary = dict(base=BASE,head=head,tree=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=ROOT,text=True).strip(),
                       leanVersion=version.strip(),pinSha256=sha(args.pin),archiveSha256=sha(args.archive),
                       declarationCount=len(rows),constantKinds=dict(sorted(Counter(r['constantKind'] for r in rows).items())),
                       fieldCount=sum(len(r['fields']) for r in rows),snapshotSha256=sha(evidence/'roadmap-census.json'),
                       sourceSha256={str(p):sha(ROOT/p) for p in modules+[SCOPE/'Census.lean']},
                       limitation='Kernel namespace census includes generated declarations; no final G49/G50 statement selection, ownership or progress assertion.')
        assert head == subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
        assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],cwd=ROOT)
        (evidence/'summary.json').write_text(json.dumps(summary,sort_keys=True,indent=2)+'\n')
        manifest = {str(p.relative_to(evidence)):sha(p) for p in sorted(evidence.rglob('*')) if p.is_file() and p.name!='sha256.json'}
        (evidence/'sha256.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
        print('H62_READ_ONLY_CENSUS_PASS',len(rows),'declarations;',summary['fieldCount'],'fields')

if __name__=='__main__':
    main()
