#!/usr/bin/env python3
"""Guard stale lazy EVM equations masquerading as checked native witnesses.

Rebuild the whole current Source/callee/native closure in one isolated library.
No Lake/project cache, prior receipt, copied object or historical export is an
input. Check both sibling import orders and all local witness theorem axioms.
Run through bounded.py for the unchanged serial memory/time policy. This is
proof checking of closed fixtures, not full H121 adequacy or a runtime gate.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[4]
_HELPER = Path(__file__).with_name('check_source_void.py')
_HELPER_BYTES = _HELPER.read_bytes()
_spec = importlib.util.spec_from_file_location('fresh_native_source', _HELPER)
s = importlib.util.module_from_spec(_spec)
exec(compile(_HELPER_BYTES, str(_HELPER), 'exec'), s.__dict__)
s.LOADED_HELPER_BYTES[_HELPER.resolve()] = _HELPER_BYTES
m = s.m


def sibling_probes():
    return [('Solidity.Evm.MachineV2', 'Solidity.Evm.Signed'),
            ('Solidity.Evm.Signed', 'Solidity.Evm.MachineV2')]


def direct_objects(imports, library, project_modules, expected):
    """Refuse a project import before its exact staged object exists."""
    result = {}
    for name in imports:
        artifact = library / (name.replace('.', '/') + '.olean')
        if name in project_modules:
            if not artifact.is_file():
                raise ValueError('missing staged project import: ' + name)
            pin = s.frame.sha(artifact)
            if expected.get(str(artifact)) != pin:
                raise ValueError('staged import differs from compiled object: ' + name)
            result[str(artifact)] = pin
        elif name.split('.')[0] not in {'Init', 'Lean', 'Std'}:
            raise ValueError('unplanned non-SDK import: ' + name)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError('evidence must remain private')
    s.configure_callable()
    order, pins = s.closure()
    local = s.local_plan()
    # Admit every exact source before elaborating any project module.
    plan = [(file[:-5], file) for file in order] + local
    modules = {name.replace('/', '.') for name, _ in plan}
    if len(modules) != len(plan):
        raise ValueError('duplicate staged module name')
    raw = {file: (ROOT / file).read_bytes() for _, file in plan}
    expected = {file: s.frame.digest(data) for file, data in raw.items()}
    for file, pin in pins.items():
        if expected[file] != pin['source_sha256']:
            raise ValueError('source changed during closure admission')
    s.frame.inventory(raw[s.frame.SOURCE])
    s.inventory(raw[s.SOURCE])
    names = []
    for _, file in local:
        rows = m.joint.export.census.declarations_text(file, raw[file].decode())
        if not rows:
            raise ValueError('empty local theorem inventory: ' + file)
        names.extend(row['source_name'] for row in rows)
    if len(names) != len(set(names)):
        raise ValueError('duplicate local theorem identity')
    out.mkdir(parents=True, exist_ok=False)
    library = out / 'library'
    library.mkdir()
    protected, helpers = s.capture_tools([s], out)
    own = Path(__file__).resolve()
    own_raw = own.read_bytes()  # The CLI/Python bootstrap remains trusted.
    saved = out / 'helper-sources' / own.relative_to(ROOT)
    saved.parent.mkdir(parents=True, exist_ok=True)
    saved.write_bytes(own_raw)
    protected.update({str(own): s.frame.digest(own_raw),
                      str(saved): s.frame.digest(own_raw)})
    protected.update({str(ROOT / f): pin for f, pin in expected.items()})
    protected[str(m.check.LEAN)] = s.frame.sha(m.check.LEAN)
    protected[str(ROOT / 'lean-toolchain')] = s.frame.sha(ROOT / 'lean-toolchain')
    env = m.profile.isolated_environment(os.environ, library)
    sdk = subprocess.check_output([str(m.check.LEAN), '--print-prefix'], env=env, text=True).strip()
    if Path(sdk).resolve() != m.check.LEAN.resolve().parent.parent:
        raise ValueError('SDK mismatch')
    artifacts, steps = {}, []

    def run(tag, staged, artifact=None):
        dependencies = direct_objects(m.profile.imports(staged.read_text()), library, modules, protected)
        cmd = [str(m.check.LEAN), '-j1', '--tstack=131072', '--root=' + str(out / 'staged')]
        if staged.name == 'TermSize.lean':
            cmd += ['-DElab.async=false']
        if artifact:
            cmd += ['-o', str(artifact)]
        cmd.append(str(staged))
        log = out / (tag + '.log')
        with log.open('w') as stream:
            done = subprocess.run(cmd, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
        m.check.verify_hashes(dependencies)
        payload = log.read_bytes()
        protected[str(log)] = s.frame.digest(payload)
        steps.append({'command': cmd, 'exit': done.returncode,
                      'log': str(log), 'sha256': protected[str(log)],
                      'direct_import_artifact_sha256': dependencies})
        if done.returncode:
            raise SystemExit('FRESH_NATIVE_FAIL ' + str(log))
        return payload.decode()

    for module, file in plan:
        staged = out / 'staged' / (module + '.lean')
        artifact = library / (module + '.olean')
        staged.parent.mkdir(parents=True, exist_ok=True)
        artifact.parent.mkdir(parents=True, exist_ok=True)
        staged.write_bytes(raw[file])
        if staged.read_bytes() != raw[file]:
            raise ValueError('staged source substitution')
        protected[str(staged)] = expected[file]
        run(module.replace('/', '_'), staged, artifact)
        dependencies = steps[-1]['direct_import_artifact_sha256']
        artifacts[file] = {'source_sha256': expected[file],
                           'artifact_sha256': s.frame.sha(artifact),
                           'direct_import_artifact_sha256': dependencies}
        protected[str(artifact)] = artifacts[file]['artifact_sha256']
    probe = out / 'staged' / 'FreshNativeWitnesses.lean'
    probe.write_text('import ' + local[-1][0] + '\n' +
                     ''.join('#print axioms ' + name + '\n' for name in names))
    protected[str(probe)] = s.frame.sha(probe)
    axioms = m.joint.parse_axioms(run('all-local-axioms', probe), '', names)
    for index, imports in enumerate(sibling_probes()):
        probe = out / 'staged' / ('SiblingImports' + str(index) + '.lean')
        probe.write_text(''.join('import ' + name + '\n' for name in imports) +
                         '#check Solidity.Evm.Instr.step.eq_43\n')
        protected[str(probe)] = s.frame.sha(probe)
        run('sibling-imports-' + str(index), probe)
    m.check.verify_hashes(protected)
    if s.closure() != (order, pins):
        raise ValueError('current closure drift')
    result = {'status': 'pass', 'mode': 'fresh-current-native-closure',
              'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'source_pins': pins, 'project_order': order, 'local_plan': local,
              'reused_objects': {}, 'artifacts': artifacts, 'steps': steps,
              'axioms': axioms, 'import_orders': sibling_probes(),
              'helper_source_bindings': helpers, 'protected_sha256': protected,
              'sdk_root': sdk, 'original_obligations_discharged': 0,
              'full_ro_adequacy': False, 'runtime_gate_pass': False,
              'trust_boundary': 'SDK/Python/stdlib/CLI bootstrap trusted; no remote attestation'}
    (out / 'receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print('FRESH_NATIVE_PASS project=' + str(len(order)) + ' local=' + str(len(local)) +
          ' reused=0 axioms=' + str(len(axioms)))


if __name__ == '__main__':
    main()
