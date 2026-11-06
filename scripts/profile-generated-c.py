#!/usr/bin/env python3
"""Build diagnostic C timers around the native walk and auxiliary checker.

BENCH_HOT_OPT=-O0 or -O2 affects only ProvesDerive and TacticSyntax. Other
translation units retain BENCH_C_OPT (default -O0). This does not change the
Lean kernel or accept the walk's unchecked result as a program proof.
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
hot_optimization = os.environ.get('BENCH_HOT_OPT', '-O0')
if hot_optimization not in ('-O0','-O2'): raise ValueError('bad hot optimization')
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
    unit_optimization = optimization
    targets = {
      'Solidity.Calculus.ProvesDerive': ('l_Solidity_Seq_residueQuoteWithin___redArg', 'WALK'),
      'Solidity.Calculus.TacticSyntax': ('l_Solidity_Derive_kernelLemma', 'AUX')}
    if module in targets:
        symbol, label = targets[module]
        pattern = r'(LEAN_EXPORT lean_object\* '+re.escape(symbol)+r'\(([^;\n]*)\)) \{\n'
        body = raw.decode()
        match = re.search(pattern, body)
        if not match: raise RuntimeError('C timing symbol missing '+symbol)
        signature, args = match[1], match[2]
        body, count = re.subn(pattern, lambda m: m[1].replace(symbol,symbol+'__cprobe_original')+' {\n',body)
        if count != 1: raise RuntimeError('C timing symbol ambiguous')
        call_args = ', '.join(re.findall(r'\bx_\d+\b',args))
        header = '#include <lean/lean.h>\nextern int printf(const char*, ...);\nextern lean_object* lean_io_mono_nanos_now(lean_object*);\nstatic uint64_t cprobe_now(void) { lean_object* r=lean_io_mono_nanos_now(lean_box(0)); uint64_t t=lean_uint64_of_nat(lean_ctor_get(r,0)); lean_dec(r); return t; }\nstatic unsigned long long cprobe_count=0;\n'
        wrapper = signature+' { uint64_t start=cprobe_now(); lean_object* result='+symbol+'__cprobe_original('+call_args+'); uint64_t elapsed=cprobe_now()-start; printf("NATIVE_C_'+label+' %llu %llu\\n",++cprobe_count,(unsigned long long)elapsed); return result; }\n'
        raw = (header+body+'\n'+wrapper).encode()
        source = output / (label+'.probe.c')
        source.write_bytes(raw)
        unit_optimization = hot_optimization
    digest = hashlib.sha256(raw).hexdigest()
    key = hashlib.sha256((digest + version + unit_optimization + "-DLEAN_EXPORTING").encode()).hexdigest()
    obj = output / (key + '.o')
    if not obj.exists():
        temporary = obj.with_suffix('.tmp.o')
        subprocess.run([str(prefix / 'bin/leanc'), unit_optimization, '-DLEAN_EXPORTING', '-c', str(source), '-o', str(temporary)], check=True)
        temporary.replace(obj)
    objects.append(str(obj))
    inputs.append({'module': module, 'cSha256': digest, 'optimization': unit_optimization})
    print(f'{index + 1}/{len(modules)} {module}', flush=True)
plugin = output / 'libSolidity_Frontend_Testing.so'
subprocess.run([str(prefix / 'bin/leanc'), '-shared', '-o', str(plugin), *objects], check=True)
(output / 'build.json').write_text(json.dumps({
    'hotOptimization':hot_optimization,'leanCommit': version, 'optimization': optimization, 'nativeProbe': os.environ.get('BENCH_NATIVE_PROBE') == '1', 'modules': inputs,
    'pluginSha256': hashlib.sha256(plugin.read_bytes()).hexdigest()
}, indent=2) + '\n')
print(plugin, flush=True)
