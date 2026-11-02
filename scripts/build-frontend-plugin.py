#!/usr/bin/env python3
"""Compile the existing frontend C closure into an optional native Lean plugin.

This is a benchmark control, not a website backend or a replacement checker.
Compile one translation unit at a time under the caller's memory guard.
"""
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import sys

prefix = Path(sys.argv[1]).resolve()
output = Path(sys.argv[2] if len(sys.argv) > 2 else '.lake/frontend-native').resolve()
output.mkdir(parents=True, exist_ok=True)
setup = json.loads(Path('.lake/build/ir/Solidity/Frontend/Testing.setup.json').read_text())
modules = sorted({name for name in setup['importArts'] if name.startswith('Solidity.')}
                 | {'Solidity.Frontend.Testing'})
optimization = os.environ.get('BENCH_C_OPT', '-O0')
if optimization not in ('-O0', '-O1', '-O2', '-O3'):
    raise ValueError('Invalid BENCH_C_OPT')
version = subprocess.check_output([str(prefix / 'bin/lean'), '--githash'], text=True).strip()
objects = []
inputs = []
for index, module in enumerate(modules):
    source = Path('.lake/build/ir') / (module.replace('.', '/') + '.c')
    raw = source.read_bytes()
    if os.environ.get('BENCH_NATIVE_PROBE') == '1' and module == 'Solidity.Frontend.Testing':
        pattern = r'(LEAN_EXPORT lean_object\* l_Solidity_Frontend_elabSolkeyTest\([^;\n]*\) \{\n)'
        marker = 'puts("NATIVE_FRONTEND_PROBE");\n'
        text, count = re.subn(pattern, lambda match: match[0] + marker, raw.decode())
        if count != 1:
            raise RuntimeError('Native entrypoint marker did not match exactly once')
        text = 'extern int puts(const char*);\n' + text
        source = output / 'Testing.probe.c'
        source.write_text(text)
        raw = text.encode()
    digest = hashlib.sha256(raw).hexdigest()
    key = hashlib.sha256((digest + version + optimization + "-DLEAN_EXPORTING").encode()).hexdigest()
    obj = output / (key + '.o')
    if not obj.exists():
        temporary = obj.with_suffix('.tmp.o')
        subprocess.run([str(prefix / 'bin/leanc'), optimization, '-DLEAN_EXPORTING', '-c', str(source), '-o', str(temporary)], check=True)
        temporary.replace(obj)
    objects.append(str(obj))
    inputs.append({'module': module, 'cSha256': digest})
    print(f'{index + 1}/{len(modules)} {module}', flush=True)
plugin = output / 'libSolidity_Frontend_Testing.so'
subprocess.run([str(prefix / 'bin/leanc'), '-shared', '-o', str(plugin), *objects], check=True)
(output / 'build.json').write_text(json.dumps({
    'leanCommit': version, 'optimization': optimization, 'nativeProbe': os.environ.get('BENCH_NATIVE_PROBE') == '1', 'modules': inputs,
    'pluginSha256': hashlib.sha256(plugin.read_bytes()).hexdigest()
}, indent=2) + '\n')
print(plugin, flush=True)
