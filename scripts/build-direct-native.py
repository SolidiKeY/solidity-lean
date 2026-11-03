#!/usr/bin/env python3
"""Build the same import-free generated-C closure for the desktop CPU.

Usage: build-direct-native.py NATIVE_LEAN_PREFIX PINNED_LEAN_SOURCE OUTPUT
The source checkout supplies stage0/stdlib's generated C, not serialized modules.
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

root = pathlib.Path(__file__).resolve().parent.parent
prefix, source, output = (pathlib.Path(p).resolve() for p in sys.argv[1:])
commit = '797c613eb9b6d4ec95db23e3e00af9ac6657f24b'
assert subprocess.check_output([str(prefix/'bin/lean'), '--githash'], text=True).strip() == commit
assert subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip() == commit
output.mkdir(parents=True, exist_ok=True)
subprocess.run([str(prefix/'bin/lake'), 'build', 'Solidity.Tools.DirectRuntime'], cwd=root,
               env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)
stage = output/'runtime'
(stage/'lib').mkdir(parents=True, exist_ok=True)
if not (stage/'lib/temp').exists():
    (stage/'lib/temp').symlink_to(source/'stage0/stdlib', target_is_directory=True)
spec = importlib.util.spec_from_file_location('direct_closure', root/'scripts/direct-runtime-closure.py')
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
symbols = subprocess.check_output(['nm', '--undefined-only', '--format=posix', str(prefix/'lib/lean/libleanrt.a')], text=True)
inputs, closure = helper.extract(root, stage, native_roots=set(re.findall(r'^(\w+) U ', symbols, re.M)))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
setup = json.loads((root/'.lake/build/ir/Solidity/Tools/DirectRuntime.setup.json').read_text())
names = sorted({n for n in setup['importArts'] if n.startswith('Solidity.')} | {'Solidity.Tools.DirectRuntime'})
sources = [{'module': n, 'sourceSha256': sha(root/(n.replace('.', '/')+'.lean')),
            'cSha256': sha(root/'.lake/build/ir'/(n.replace('.', '/')+'.c'))} for n in names]
flags = ['-O2', '-ffunction-sections', '-fdata-sections', '-I'+str(prefix/'include')]
compiler = prefix/'bin/leanc'
identity = sha(prefix/'bin/clang') + sha(prefix/'include/lean/config.h')
objects = []
for i, (name, text, original, expected) in enumerate(inputs):
    if sha(original) != expected: raise ValueError('Changed generated source: '+name)
    key = hashlib.sha256((text+str(flags)+identity).encode()).hexdigest()
    obj = output/(key+'.o')
    if not obj.exists():
        snapshot = output/(key+'.c')
        snapshot.write_text(text)
        temporary = output/(key+'.tmp.o')
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
bridge = output/'bridge.o'
subprocess.run([os.environ.get('CC', 'cc'), *flags, '-DSOLIDITY_DIRECT_NATIVE', '-c',
                str(root/'web/browser/direct-bridge.c'), '-o', str(bridge)], check=True)
subprocess.run([str(compiler), *flags, '-DSOLIDITY_DIRECT_NATIVE',
                str(bridge), str(output/'initialize.c'), *objects,
                '-Wl,--gc-sections', '-o', str(executable)+'.tmp'], check=True)
for _, _, original, expected in inputs:
    if sha(original) != expected: raise ValueError('Changed generated source during compilation')
for entry in sources:
    if sha(root/(entry['module'].replace('.', '/')+'.lean')) != entry['sourceSha256']:
        raise ValueError('Changed source during compilation')
pathlib.Path(str(executable)+'.tmp').replace(executable)
manifest = {'version': 1, 'toolchain': (root/'lean-toolchain').read_text().strip(),
            'leanCommit': commit, 'platform': sys.platform, 'arch': platform.machine(),
            'sourceFiles': sources, 'executable': sha(executable), 'closure': closure,
            'optimization': '-O2', 'bridgeSha256': sha(root/'web/browser/direct-bridge.c')}
(output/'build.json').write_text(json.dumps(manifest, indent=2)+'\n')
licenses = output/'licenses'
licenses.mkdir(exist_ok=True)
for name in ['LICENSE', 'LICENSES']:
    shutil.copyfile(prefix/name, licenses/('Lean-'+name+'.txt'))
print(json.dumps({'bytes': executable.stat().st_size, 'closure': closure}), flush=True)
