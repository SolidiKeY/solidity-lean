#!/usr/bin/env python3
"""Build a pure native API for one generated exact-obligation input module.
Usage: verify-build.py LEAN_PREFIX PINNED_LEAN_SOURCE INPUT_LEAN OUTPUT
The existing closure extractor rejects effects and unresolved callbacks.
"""
import hashlib
import importlib.util
import json
import os
import pathlib
import platform
import re
import subprocess
import shutil
import sys
import tempfile
from verify_artifacts import runtime_aliases

for override in ['LEAN_CC','LEAN_SYSROOT','CPATH','C_INCLUDE_PATH','CPLUS_INCLUDE_PATH','LIBRARY_PATH','COMPILER_PATH']:
    if os.environ.get(override):
        raise ValueError('Unpinned compiler override: '+override)
root = pathlib.Path(__file__).resolve().parent.parent
prefix, source, input_source, output = (pathlib.Path(p).resolve() for p in sys.argv[1:])
module = input_source.stem
if not re.fullmatch(r"VerifyInput[0-9a-f]{64}", module): raise ValueError("Invalid generated module name")
fixture = input_source.parent/"source.ast.json"
commit = '797c613eb9b6d4ec95db23e3e00af9ac6657f24b'
if subprocess.check_output([str(prefix/'bin/lean'), '--githash'], text=True).strip() != commit:
    raise ValueError('Lean compiler does not match pinned revision')
def check_source():
    if subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip() != commit:
        raise ValueError('Lean source does not match pinned revision')
    if subprocess.check_output(['git', '-C', str(source), 'status', '--porcelain'], text=True).strip():
        raise ValueError('Pinned Lean source has local changes')
check_source()
closure_path=root/'scripts/direct-runtime-closure.py'
closure_bytes=closure_path.read_bytes()
spec = importlib.util.spec_from_file_location('direct_closure', closure_path)
helper = importlib.util.module_from_spec(spec)
exec(compile(closure_bytes,str(closure_path),'exec'),helper.__dict__)
bridge_path=root/'web/browser/direct-bridge.c'
bridge_bytes=bridge_path.read_bytes()
cc=shutil.which(os.environ.get('CC','cc'))
if not cc: raise ValueError('System C compiler not found')
def provenance_paths():
    return [pathlib.Path(__file__).resolve(), root/'scripts/verify_artifacts.py', closure_path, bridge_path, root/'lean-toolchain', root/'lakefile.toml',
            pathlib.Path(cc), *[prefix/'bin'/n for n in ['lean','lake','leanc','clang','ld.lld','llvm-ar']],
            *sorted((prefix/'include').rglob('*.h')),
            *sorted((prefix/'lib').rglob('*.a'))]
provenance=helper.snapshot_files(provenance_paths())
if provenance[str(closure_path)]!=hashlib.sha256(closure_bytes).hexdigest(): raise ValueError('Closure changed before snapshot')
if provenance[str(bridge_path)]!=hashlib.sha256(bridge_bytes).hexdigest(): raise ValueError('Bridge changed before snapshot')
input_snapshot=helper.snapshot_files([input_source,fixture])
source_snapshot=helper.snapshot_files((root/'Solidity').rglob('*.lean'))
output.mkdir(parents=True, exist_ok=True)
subprocess.run([str(prefix/'bin/lake'), 'build', 'Solidity.Tools.FastMode.Engine'], cwd=root,
               env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)
input_c = output/(module+'.c')
setup = json.loads(subprocess.check_output([str(prefix/'bin/lake'), '--quiet', 'setup-file', str(input_source)],
    cwd=root, env=dict(os.environ, LEAN_NUM_THREADS='1'), text=True))
# Query paired C/olean facets from the current build graph. Default cached
# builds need not restore C into .lake/build/ir, so the extractor gets an owned
# overlay of selected artifacts instead of reading those fixed local paths.
modules=sorted(setup['importArts'])
if not modules or any(not name.startswith('Solidity.') for name in modules):
    raise ValueError('Unexpected ordinary native import closure')
targets=[name+':'+facet for name in modules for facet in ['c','olean']]
artifacts=subprocess.check_output([str(prefix/'bin/lake'),'--quiet','query',*targets],
    cwd=root,env=dict(os.environ,LEAN_NUM_THREADS='1'),text=True).splitlines()
if len(artifacts)!=len(targets):raise ValueError('Unexpected ordinary artifact query count')
c_paths={name:pathlib.Path(artifacts[2*i]).resolve() for i,name in enumerate(modules)}
compiled_imports={name:[artifacts[2*i+1]] for i,name in enumerate(modules)}
if any(not path.is_file() or path.suffix!='.c' for path in c_paths.values()):
    raise ValueError('Unexpected ordinary native C artifact query')
selected=helper.snapshot_files([*c_paths.values(),
    *(pathlib.Path(p).resolve() for paths in compiled_imports.values() for p in paths)])
frozen={str(pathlib.Path(p).resolve()):pathlib.Path(p).read_bytes()
        for paths in compiled_imports.values() for p in paths}
aliases=runtime_aliases(compiled_imports,setup['importArts'],frozen)
selected.update({path:hashlib.sha256(raw).hexdigest() for path,raw in aliases.items()})
selected_tree=tempfile.TemporaryDirectory(prefix='selected-',dir=output)
selected_root=pathlib.Path(selected_tree.name)
for name,path in c_paths.items():
    link=selected_root/'.lake/build/ir'/(name.replace('.','/')+'.c')
    link.parent.mkdir(parents=True,exist_ok=True);link.symlink_to(path)
setup['name'] = module
setup_path=output/(module+'.setup.json')
setup_path.write_text(json.dumps(setup)+'\n')
subprocess.run([str(prefix/'bin/lean'), '--setup='+str(setup_path), '--tstack=131072', '-j1',
               '-o', str(output/(module+'.olean')), '-c', str(input_c), str(input_source)],
               cwd=root, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)
stage = output/'runtime'
temporary = stage/'lib/temp'
temporary.mkdir(parents=True, exist_ok=True)
for entry in (source/'stage0/stdlib').iterdir():
    destination = temporary/entry.name
    if destination.is_symlink(): destination.unlink()
    if destination.exists(): raise ValueError('Unexpected build staging file: '+str(destination))
    destination.symlink_to(entry, target_is_directory=entry.is_dir())
generated_link=temporary/(module+'.c')
if generated_link.is_symlink(): generated_link.unlink()
if generated_link.exists(): raise ValueError('Unexpected generated C staging file')
generated_link.symlink_to(input_c)
symbols = subprocess.check_output(['nm', '--undefined-only', '--format=posix', str(prefix/'lib/lean/libleanrt.a')], text=True)
inputs, closure = helper.extract(selected_root, stage, module=module, native_roots=set(re.findall(r'^(\w+) U ', symbols, re.M)))
sha = helper.file_sha256
names = sorted(name for name in helper.collect(selected_root, stage, module)[0] if name.startswith('Solidity.'))
sources = [{'module': n, 'sourceSha256': source_snapshot[str(root/(n.replace('.', '/')+'.lean'))],
            'cPath': str(c_paths[n]), 'cSha256': selected[str(c_paths[n])]} for n in names]
flags = ['-O2', '-ffunction-sections', '-fdata-sections', '-I'+str(prefix/'include')]
compiler = prefix/'bin/leanc'
identity = json.dumps(provenance,sort_keys=True)
objects = []
for i, (name, text, original, expected) in enumerate(inputs):
    if sha(original) != expected: raise ValueError('Changed generated source: '+name)
    key = hashlib.sha256((text+str(flags)+identity).encode()).hexdigest()
    objects_dir=root/'.lake/verify/objects'
    objects_dir.mkdir(parents=True, exist_ok=True)
    obj = objects_dir/(key+'.o')
    if not obj.exists():
        snapshot = objects_dir/(key+'.c')
        snapshot.write_text(text)
        temporary = objects_dir/(key+'.tmp.o')
        subprocess.run([str(compiler), *flags, '-c', str(snapshot), '-o', str(temporary)], check=True)
        temporary.replace(obj)
        snapshot.unlink()
    objects.append(str(obj))
    print(f'{i+1}/{len(inputs)} {name}', flush=True)
init = '#include <lean/lean.h>\n'
for name, *_ in inputs:
    init += 'extern lean_object* initialize_'+name.replace('.', '_')+'(uint8_t,lean_object*);\n'
init += 'lean_object* compact_initialize(void) { lean_object* res;\n'
for name, *_ in inputs:
    init += 'res=initialize_'+name.replace('.', '_')+'(1,lean_io_mk_world());if(lean_io_result_is_error(res))return res;lean_dec(res);\n'
init += 'return lean_io_result_mk_ok(lean_box(0));}\n'
(output/'initialize.c').write_text(init)
executable = output/'direct-check'
# Lean's bundled clang deliberately omits the platform's stdio headers.
# Compile the small line-protocol host with the system C compiler; generated
# Lean C and the final link continue to use the pinned leanc.
bridge_source = output/('bridge-'+hashlib.sha256(bridge_bytes).hexdigest()+'.c')
bridge_source.write_bytes(bridge_bytes)
bridge = output/'bridge.o'
subprocess.run([cc, *flags, '-DSOLIDITY_DIRECT_NATIVE', '-c',
                str(bridge_source), '-o', str(bridge)], check=True)
subprocess.run([str(compiler), *flags, '-DSOLIDITY_DIRECT_NATIVE',
                str(bridge), str(output/'initialize.c'), *objects,
                '-Wl,--gc-sections', '-o', str(executable)+'.tmp'], check=True)
for _, _, original, expected in inputs:
    if sha(original) != expected: raise ValueError('Changed generated source during compilation')
for entry in sources:
    if sha(root/(entry['module'].replace('.', '/')+'.lean')) != entry['sourceSha256']:
        raise ValueError('Changed source during compilation')
helper.verify_snapshot(selected,selected.keys())
helper.verify_snapshot(provenance,provenance_paths())
helper.verify_snapshot(input_snapshot,[input_source,fixture])
helper.verify_snapshot(source_snapshot,(root/'Solidity').rglob('*.lean'))
check_source()
pathlib.Path(str(executable)+'.tmp').replace(executable)
manifest = {'version': 2, 'rootModule': module,
            'generatedInput': {'path': str(input_source), 'sha256': input_snapshot[str(input_source)]},
            'generatedFixture': {'path': str(fixture), 'sha256': input_snapshot[str(fixture)]}, 'toolchain': (root/'lean-toolchain').read_text().strip(),
            'leanCommit': commit, 'platform': sys.platform, 'arch': platform.machine(),
            'sourceFiles': sources, 'executable': sha(executable), 'closure': closure,
            'optimization': '-O2', 'bridgeSha256': hashlib.sha256(bridge_bytes).hexdigest(),
            'closureScriptSha256': hashlib.sha256(closure_bytes).hexdigest(),
            'buildInputs': provenance, 'selectedArtifacts': selected, 'compilerCommand': cc}
(output/'build.json').write_text(json.dumps(manifest, indent=2)+'\n')
licenses = output/'licenses'
licenses.mkdir(exist_ok=True)
for name in ['LICENSE', 'LICENSES']:
    shutil.copyfile(prefix/name, licenses/('Lean-'+name+'.txt'))
print(json.dumps({'bytes': executable.stat().st_size, 'closure': closure}), flush=True)
