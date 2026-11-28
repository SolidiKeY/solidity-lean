#!/usr/bin/env python3
"""Build the thin driver without changing shared Lake targets.
Usage under the repository writer lock: python3 scripts/differential-yul/build-driver.py NEW_EXTERNAL_DIR
Lean/Lake must be on PATH. Build serially with 12 GiB address-space bound.
The manifest identifies selected build inputs, not a compiler-correctness proof.
"""
import hashlib, json, os, pathlib, resource, shutil, subprocess, sys
root = pathlib.Path(__file__).resolve().parents[2]
if len(sys.argv) != 2:
    raise SystemExit(__doc__)
out = pathlib.Path(sys.argv[1]).resolve()
if out == root or root in out.parents:
    raise SystemExit('build outputs must be outside checkout')
if not out.parent.is_dir():
    raise SystemExit('output parent must exist')
out.mkdir(mode=0o700)
env = dict(os.environ, LEAN_NUM_THREADS='1')
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
bound = 12 * 1024**3
bound = min([bound] + [limit for limit in (soft, hard) if limit != resource.RLIM_INFINITY])
resource.setrlimit(resource.RLIMIT_AS, (bound, hard))
lean = shutil.which('lean')
if not lean:
    raise SystemExit('pinned lean must be on PATH')
bin_dir = pathlib.Path(lean).resolve().parent
lake, lean, leanc = [str(bin_dir / name) for name in ('lake','lean','leanc')]
def run(args):
    return subprocess.check_output(args, cwd=root, env=env, text=True)
if run([lean,'--githash']).strip() != '797c613eb9b6d4ec95db23e3e00af9ac6657f24b':
    raise SystemExit('wrong Lean compiler revision')
driver = root / 'scripts/differential-yul/Driver.lean'
setup = json.loads(run([lake,'--quiet','setup-file',str(driver)]))
modules = sorted(setup['importArts'])
if not modules or 'Solidity.Yul.StatefulImport' not in modules:
    raise SystemExit('missing stateful import closure')
def digest(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()
sources = [driver, pathlib.Path(__file__).resolve(), root/'lean-toolchain', root/'lakefile.toml']
sources += [root / (name.replace('.','/') + '.lean') for name in modules]
snapshot = {str(p):digest(p) for p in sources}
objects = [json.loads(line) for line in run([lake,'--json','query',*[f'+{m}:o' for m in modules]]).splitlines() if line.strip()]
if len(objects) != len(modules) or any(not isinstance(p,str) or not pathlib.Path(p).is_file() for p in objects):
    raise SystemExit('invalid object closure from Lake')
source_c = out/'Driver.c'
run([lake,'lean',str(driver),'--','--tstack=131072','-j1','-M12288','-c',str(source_c)])
subprocess.run([leanc,'-O3','-o',str(out/'driver'),str(source_c),*objects],cwd=root,env=env,check=True)
if snapshot != {str(p):digest(p) for p in sources}:
    raise SystemExit('source changed during build')
manifest = {'schema':1,'leanVersion':run([lean,'--version']).strip(),
    'lakeVersion':run([lake,'--version']).strip(),'sources':snapshot,
    'objects':{str(pathlib.Path(p).resolve()):digest(p) for p in objects},
    'executableSha256':digest(out/'driver'),'generatedCSha256':digest(source_c),
    'tools':{p:digest(p) for p in (lake,lean,leanc)},
    'boundary':'Native execution artifact; no proof of Lean compiler or external EVM agreement.'}
(out/'build.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(out/'driver')
