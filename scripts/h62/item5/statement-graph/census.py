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
from owner_overlay import prepare, REL_PATH

if not __debug__:
    raise RuntimeError('H62 verification cannot run with Python optimization enabled')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ('lean-bin','pin','archive','evidence'):
        parser.add_argument('--'+arg,type=Path,required=True)
    parser.add_argument('--area',choices=('roadmap','evm'),default='roadmap')
    parser.add_argument('--hash-owner-overlay',action='store_true',help='H70 exact-base relay in an off-checkout source copy; roadmap area only')
    args = parser.parse_args()
    if args.hash_owner_overlay and args.area != 'roadmap':
        parser.error('--hash-owner-overlay is only needed for roadmap')
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
        if args.area == 'evm':
            modules = [Path('Solidity/Keccak.lean'),Path('Solidity/Roadmap/Evm.lean'),SCOPE/'Exporter.lean']
        driver = SCOPE/('EvmCensus.lean' if args.area == 'evm' else 'Census.lean')
        snapshot_name = args.area+'-census'
        overlay = None
        overlay_source = None
        if args.hash_owner_overlay:
            overlay_source,overlay = prepare(evidence/'owner-overlay-source')
            (evidence/'owner-overlay.json').write_text(json.dumps(overlay,indent=2)+'\n')
        original_hashes = {str(p):sha(ROOT/p) for p in modules+[driver]}
        validation_hashes = dict(original_hashes)
        if overlay is not None:
            validation_hashes[str(REL_PATH)] = overlay['targetSha256']
        import hashlib
        input_material = dict(tree=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=ROOT,text=True).strip(),
                              sources=validation_hashes,pinSha256=sha(args.pin),
                              patchSha256=overlay['patchSha256'] if overlay else None)
        input_digest = hashlib.sha256(json.dumps(input_material,sort_keys=True,separators=(',',':')).encode()).hexdigest()
        inputs = dict(base=BASE,head=head,tree=input_material['tree'],area=args.area,leanVersion=version.strip(),
                      pinSha256=sha(args.pin),archiveSha256=sha(args.archive),ownerOverlay=overlay,
                      sourceSha256=original_hashes,validationSourceSha256=validation_hashes,validationInputSha256=input_digest)
        (evidence/'inputs.json').write_text(json.dumps(inputs,sort_keys=True,indent=2)+'\n')
        logs = []
        def run(src,output=None,package_root=None):
            assert available() >= 4*1024**3, '4GiB reserve missing'
            cmd = [lean,'-j1','--tstack=131072']
            if package_root is not None:
                cmd += ['-R',str(package_root)]
            if output is not None:
                output.parent.mkdir(parents=True,exist_ok=True)
                cmd += ['-o',str(output)]
            cmd += [str(src)]
            started = time.monotonic()
            logfile = evidence/(src.stem+'.log')
            def bound():
                resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3))
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
            originals_match = all(sha(ROOT/p)==h for p,h in original_hashes.items())
            same_head = head == subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
            clean = not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],cwd=ROOT)
            logs.append(dict(command=cmd,exit=proc.returncode,seconds=time.monotonic()-started,log=str(logfile),
                             originalSourcesUnchanged=originals_match,headUnchanged=same_head,checkoutClean=clean))
            (evidence/'commands.json').write_text(json.dumps(logs,indent=2)+'\n')
            assert originals_match and same_head and clean, 'source checkout changed during validation'
            assert proc.returncode == 0, logs[-1]
        for src in modules:
            if overlay_source is not None and src == REL_PATH:
                run(overlay_source,build/src.with_suffix('.olean'),evidence/'owner-overlay-source')
            else:
                run(src,build/src.with_suffix('.olean'))
        run(driver)
        assert (evidence/(snapshot_name+'.json')).read_bytes() == (evidence/(snapshot_name+'-repeat.json')).read_bytes(), 'census nondeterminism'
        snapshot = json.loads((evidence/(snapshot_name+'.json')).read_text())
        rows = snapshot['declarations']
        summary = dict(area=args.area,base=BASE,head=head,tree=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=ROOT,text=True).strip(),
                       leanVersion=version.strip(),pinSha256=sha(args.pin),archiveSha256=sha(args.archive),
                       declarationCount=len(rows),constantKinds=dict(sorted(Counter(r['constantKind'] for r in rows).items())),
                       fieldCount=sum(len(r['fields']) for r in rows),snapshotSha256=sha(evidence/(snapshot_name+'.json')),
                       sourceSha256={str(p):sha(ROOT/p) for p in modules+[driver]},
                       limitation='Kernel namespace census includes generated declarations; no final G49/G50 statement selection, ownership or progress assertion.')
        summary['ownerOverlay'] = overlay
        summary['validationSourceSha256'] = dict(summary['sourceSha256'])
        if overlay is not None:
            summary['validationSourceSha256'][str(REL_PATH)] = overlay['targetSha256']
            summary['limitation'] += ' Uses an H70 owner proof migration in an isolated source copy; not a full migration gate.'
        import hashlib
        material = dict(tree=summary['tree'],sources=summary['validationSourceSha256'],pinSha256=summary['pinSha256'],
                        patchSha256=overlay['patchSha256'] if overlay else None)
        summary['validationInputSha256'] = hashlib.sha256(json.dumps(material,sort_keys=True,separators=(',',':')).encode()).hexdigest()
        assert all(sha(ROOT/p)==summary['sourceSha256'][str(p)] for p in modules+[driver]), 'original source changed'
        assert head == subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
        assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],cwd=ROOT)
        (evidence/'summary.json').write_text(json.dumps(summary,sort_keys=True,indent=2)+'\n')
        manifest = {str(p.relative_to(evidence)):sha(p) for p in sorted(evidence.rglob('*')) if p.is_file() and p.name!='sha256.json'}
        (evidence/'sha256.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
        print('H62_READ_ONLY_CENSUS_PASS',len(rows),'declarations;',summary['fieldCount'],'fields')

if __name__=='__main__':
    main()
