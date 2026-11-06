#!/usr/bin/env python3
"""Compile the existing frontend C closure into an optional native Lean plugin.

This optional desktop backend retains the normal kernel checker. It is not
a website backend. Build Solidity.Frontend.Testing with Lake first.
Compile one translation unit at a time under the caller's memory guard.
"""
import hashlib
import fcntl
import json
import os
import platform
import re
from pathlib import Path
import subprocess
import sys

prefix = Path(sys.argv[1]).resolve()
output = Path(sys.argv[2] if len(sys.argv) > 2 else '.lake/frontend-native').resolve()
output.mkdir(parents=True, exist_ok=True)
build_lock = (output / '.build.lock').open('a')
fcntl.flock(build_lock, fcntl.LOCK_EX)
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
    source_digest = hashlib.sha256(raw).hexdigest()
    if os.environ.get('BENCH_NATIVE_PROBE') == '1' and module == 'Solidity.Frontend.Testing':
        pattern = r'(LEAN_EXPORT lean_object\* l_Solidity_Frontend_elabSolkeyTest\([^;\n]*\) \{\n)'
        marker = 'fputs("NATIVE_FRONTEND_PROBE\\n", stderr);\n'
        text, count = re.subn(pattern, lambda match: match[0] + marker, raw.decode())
        if count != 1:
            raise RuntimeError('Native entrypoint marker did not match exactly once')
        wrappers = []
        for symbol, label in [('l_Solidity_Frontend_SpecProposal_quoteResidue___redArg', 'NATIVE_SPEC_WALK'),
                              ('l_Solidity_Frontend_directResult', 'NATIVE_DIRECT_CHECK')]:
            walk_pattern = r'(LEAN_EXPORT lean_object\* '+symbol+r'\(([^;\n]*)\)) \{\n'
            match = re.search(walk_pattern, text)
            if not match:
                raise RuntimeError('Native timer did not match: ' + symbol)
            signature, args = match[1], match[2]
            text, count = re.subn(walk_pattern, lambda m: m[1].replace(symbol, symbol+'__probe_original')+' {\n', text)
            if count != 1: raise RuntimeError('Native timer is ambiguous')
            arguments = ', '.join(re.findall(r'\bx_\d+\b', args))
            wrappers.append(signature+' { uint64_t start=probe_now(); lean_object* result='+symbol+'__probe_original('+arguments+'); uint64_t elapsed=probe_now()-start; fprintf(stderr,"'+label+' %llu\\n",(unsigned long long)elapsed); return result; }\n')
        header = '#include <lean/lean.h>\nextern void* stderr;\nextern int fputs(const char*, void*);\nextern int fprintf(void*, const char*, ...);\nextern lean_object* lean_io_mono_nanos_now(lean_object*);\nstatic uint64_t probe_now(void) { lean_object* r=lean_io_mono_nanos_now(lean_box(0)); uint64_t t=lean_uint64_of_nat(lean_ctor_get(r,0)); lean_dec(r); return t; }\n'
        text = header + text + '\n' + '\n'.join(wrappers)
        source = output / 'Testing.probe.c'
        source.write_text(text)
        raw = text.encode()
    digest = hashlib.sha256(raw).hexdigest()
    key = hashlib.sha256((digest + version + optimization + "-DLEAN_EXPORTING").encode()).hexdigest()
    obj = output / (key + '.o')
    if not obj.exists():
        temporary = obj.with_suffix('.tmp.o')
        # Compile immutable captured bytes rather than a path Lake may replace.
        snapshot = output / (digest + '.c')
        snapshot.write_bytes(raw)
        subprocess.run([str(prefix / 'bin/leanc'), optimization, '-DLEAN_EXPORTING', '-c', str(snapshot), '-o', str(temporary)], check=True)
        temporary.replace(obj)
    objects.append(str(obj))
    stem = module.replace('.', '/')
    files = [f'{stem}.lean', f'.lake/build/ir/{stem}.c']
    for extension in ('.olean', '.olean.private', '.olean.server', '.ir'):
        file = Path('.lake/build/lib/lean') / (stem + extension)
        if file.exists(): files.append(str(file))
    identities = {file: hashlib.sha256(Path(file).read_bytes()).hexdigest() for file in files}
    if identities[f'.lake/build/ir/{stem}.c'] != source_digest:
        raise RuntimeError('C input changed during native build: ' + module)
    inputs.append({'module': module, 'cSha256': digest,
                   'sourceCSha256': source_digest, 'files': identities})
    print(f'{index + 1}/{len(modules)} {module}', flush=True)
plugin = output / 'libSolidity_Frontend_Testing.so'
temporary_plugin = output / 'libSolidity_Frontend_Testing.tmp.so'
subprocess.run([str(prefix / 'bin/leanc'), '-shared', '-o', str(temporary_plugin), *objects], check=True)
for module in inputs:
    module['fileStats'] = {}
    for file, expected in module['files'].items():
        before = Path(file).stat()
        if hashlib.sha256(Path(file).read_bytes()).hexdigest() != expected:
            raise RuntimeError('Frontend changed during native build: ' + file)
        after = Path(file).stat()
        fields = lambda st: [str(st.st_dev), str(st.st_ino), str(st.st_size), str(st.st_mtime_ns), str(st.st_ctime_ns)]
        if fields(before) != fields(after):
            raise RuntimeError('Frontend changed while recording native identities: ' + file)
        module['fileStats'][file] = fields(after)
plugin_digest = hashlib.sha256(temporary_plugin.read_bytes()).hexdigest()
versioned_plugin = output / plugin_digest / 'libSolidity_Frontend_Testing.so'
versioned_plugin.parent.mkdir(exist_ok=True)
if versioned_plugin.exists():
    if hashlib.sha256(versioned_plugin.read_bytes()).hexdigest() != plugin_digest:
        raise RuntimeError('Corrupt content-addressed native cache')
    temporary_plugin.unlink()
else:
    temporary_plugin.replace(versioned_plugin)
# Keep the conventional CLI path, while LSP sessions load the immutable name.
alias = output / 'libSolidity_Frontend_Testing.alias.so'
alias.unlink(missing_ok=True)
os.link(versioned_plugin, alias)
alias.replace(plugin)
manifest = {
    'schemaVersion': 1, 'platform': sys.platform,
    'architecture': {'x86_64': 'x64', 'AMD64': 'x64', 'aarch64': 'arm64'}.get(platform.machine(), platform.machine()),
    'toolchain': Path('lean-toolchain').read_text().strip(),
    'leanCommit': version, 'optimization': optimization,
    'nativeProbe': os.environ.get('BENCH_NATIVE_PROBE') == '1', 'modules': inputs,
    'pluginSha256': plugin_digest, 'pluginFile': str(versioned_plugin.relative_to(output))
}
temporary_manifest = output / 'build.json.tmp'
temporary_manifest.write_text(json.dumps(manifest, indent=2) + '\n')
temporary_manifest.replace(output / 'build.json')
print(plugin, flush=True)
