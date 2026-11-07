#!/usr/bin/env python3
"""Guard stale evaluator/capture dependencies validating inherited fixture claims.

Recompile the real fixture import closure, refusing the historically held
Premises workload. No shared project cache fallback is available. SDK modules
are still compiler-provided dependencies, not independently source certified.
Run only under the serial bounded runner that owns resource and writer limits.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

check = load('capture_encoding_check', HERE/'check_encoding_fixture.py')
ledger = load('capture_case_ledger', HERE/'case_ledger.py')
TARGETS = ['Solidity.Lowering.Readonly.FullCaptureControls',
           'Solidity.Lowering.Readonly.CaptureFailureControls',
           'Solidity.Lowering.Readonly.EnvironmentCreditControls']
EXTRAS = {f'tests/h62/item1/readonly-bind/{name}.lean': name for name in
          ['PhaseControls', 'BindControls', 'EncodingFailureControls']}
HELD = 'Solidity.Backend.WorldCalls.Premises'


def imports(text):
    clean = ledger.census.mask(text)
    result = []
    for line in clean.splitlines():
        match = re.match(r'^\s*(?:(?:public|meta)\s+)*import\b(.*)$', line)
        if match:
            names = match[1].split()
            if not names or any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', n) for n in names):
                raise ValueError('unsupported import syntax')
            result.extend(names)
    return result


def closure(root, targets, extras):
    seen, active, order, pins = set(), set(), [], {}
    def walk(module):
        if module == HELD:
            raise ValueError('historically held workload refused: '+module)
        if module in active:
            raise ValueError('cyclic project import')
        if module in seen:
            return
        if not module.startswith('Solidity.'):
            if module.split('.')[0] not in {'Lean','Init','Std'}:
                raise ValueError('foreign dependency: '+module)
            return
        active.add(module)
        path = module.replace('.', '/')+'.lean'
        raw = (root/path).read_bytes()
        deps = imports(raw.decode())
        pins[path] = {'source_sha256': check.hashlib.sha256(raw).hexdigest(), 'imports': deps}
        for dep in deps:
            walk(dep)
        active.remove(module)
        seen.add(module)
        order.append(path)
    for target in targets:
        walk(target)
    for path in extras:
        raw = (root/path).read_bytes()
        deps = imports(raw.decode())
        for dep in deps:
            walk(dep)
        pins[path] = {'source_sha256': check.hashlib.sha256(raw).hexdigest(), 'imports': deps}
    return order, pins


def isolated_environment(ambient, library):
    result = {k: v for k, v in ambient.items()
              if not k.startswith(('LEAN_', 'ELAN_'))}
    result.update(LEAN_PATH=str(library), LEAN_NUM_THREADS='1',
                  LEAN_SYSROOT=str(check.LEAN.resolve().parent.parent))
    return result


def without_object(artifact, action):
    hidden = artifact.with_suffix('.refusal-hidden')
    if hidden.exists():
        raise ValueError('existing refusal-control artifact')
    artifact.rename(hidden)
    try:
        return action()
    finally:
        if artifact.exists():
            raise ValueError('unexpected replacement during missing-object control')
        hidden.rename(artifact)


def expected_theorems(root):
    sources = [n.replace('.', '/')+'.lean' for n in TARGETS]+list(EXTRAS)
    names = [row['source_name'] for path in sources
             for row in ledger.census.declarations_text(path, (root/path).read_text())
             if row['visibility'] == 'public']
    names += [ledger.PREFIX+name for name in ledger.CASES]
    if len(names) != len(set(names)) or len(names) != 38:
        raise ValueError('fixture/original theorem census drift')
    return names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    order, source_pins = closure(ROOT, TARGETS, EXTRAS)
    names = expected_theorems(ROOT)
    library = out/'library'
    library.mkdir()
    # No .lake project fallback or symlink scaffold: every project import must
    # resolve to one of the fresh objects in this private library.
    env = isolated_environment(os.environ, library)
    sdk = check.LEAN.resolve().parent.parent
    reported_sdk = subprocess.check_output([str(check.LEAN), '--print-prefix'],
                                           env=env, text=True).strip()
    if Path(reported_sdk).resolve() != sdk or not (sdk/'lib/lean').is_dir():
        raise ValueError('compiler sysroot differs from pinned SDK')
    input_pins = {str(p): check.sha(p) for p in [check.LEAN, ROOT/'lean-toolchain',
                  Path(__file__).resolve(), HERE/'check_encoding_fixture.py',
                  HERE/'case_ledger.py', HERE/'overlay.py', ROOT/'scripts/h62/item2/audit-readonly-calls/census.py']}
    protected = {}
    steps = []
    artifacts = {}
    def run(tag, source, artifact=None, expect_missing=None):
        command = [str(check.LEAN), '-j1', '--tstack=131072', '--root='+str(out)]
        if artifact:
            artifact.parent.mkdir(parents=True, exist_ok=True)
            command += ['-o', str(artifact)]
        command.append(str(source))
        log = out/(tag+'.log')
        with log.open('w') as stream:
            done = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
        raw = log.read_bytes()
        steps.append({'command': command, 'exit': done.returncode, 'log': str(log),
                      'sha256': check.hashlib.sha256(raw).hexdigest(),
                      'expected_missing_object': expect_missing})
        if expect_missing:
            if done.returncode == 0 or expect_missing not in raw.decode() or 'does not exist' not in raw.decode():
                raise SystemExit('PROJECT_CACHE_REFUSAL_FAIL '+str(log))
            return raw.decode()
        if done.returncode:
            raise SystemExit('CAPTURE_FIXTURES_FAIL '+str(log))
        return raw.decode()
    for relative in order+list(EXTRAS):
        module = relative[:-5] if relative in order else EXTRAS[relative]
        source = out/(module+'.lean')
        artifact = library/(module+'.olean')
        if check.sha(ROOT/relative) != source_pins[relative]['source_sha256']:
            raise ValueError('closure source changed before compile')
        record = check.compile_staged(ROOT/relative, source, artifact,
                                     lambda staged, obj: run(module.replace('/','_'), staged, obj))
        if record['source_sha256'] != source_pins[relative]['source_sha256']:
            raise ValueError('source/closure import graph drift')
        protected[str(source)] = record['source_sha256']
        protected[str(artifact)] = record['artifact_sha256']
        artifacts[relative] = record
    missing_probe = out/'NoFallback.lean'
    missing_probe.write_text('import Solidity.Source.Hoare\n')
    protected[str(missing_probe)] = check.sha(missing_probe)
    without_object(library/'Solidity/Source/Hoare.olean',
                   lambda: run('missing-project-object', missing_probe,
                               expect_missing=str(library/'Solidity/Source/Hoare.olean')))
    probe = out/'Probe.lean'
    probe.write_text(''.join('import '+m+'\n' for m in TARGETS+list(EXTRAS.values()))+
                     ''.join('#print axioms '+n+'\n' for n in names))
    protected[str(probe)] = check.sha(probe)
    log = run('axioms', probe)
    records = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", log)
    if len(records) != len(names) or {n for n, _ in records} != set(names):
        raise ValueError('missing or duplicate theorem axiom records')
    axioms = {n: [a.strip() for a in raw.split(',') if a.strip()] for n, raw in records}
    if any(set(a)-check.ALLOWED for a in axioms.values()):
        raise ValueError('unexpected axiom')
    check.verify_hashes(input_pins | protected | {step['log']: step['sha256'] for step in steps})
    check.verify_hashes({str(ROOT/p): r['source_sha256'] for p, r in source_pins.items()})
    if subprocess.check_output([str(check.LEAN),'--print-prefix'],env=env,text=True).strip() != reported_sdk:
        raise ValueError('compiler sysroot changed')
    receipt = {'boundary': __doc__, 'sdk_root': str(sdk),
               'reported_sdk_root': reported_sdk, 'sanitized_lean_environment': {
                   k: env[k] for k in ['LEAN_PATH','LEAN_SYSROOT','LEAN_NUM_THREADS']}, 'project_order': order, 'source_pins': source_pins,
               'artifacts': artifacts, 'steps': steps, 'axioms': axioms,
               'input_pins': input_pins, 'protected_sha256': protected,
               'compiler_version': subprocess.check_output([str(check.LEAN),'--version'],text=True).strip(),
               'head': subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
               'project_cache_fallback': False, 'full_goal_acceptance': False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('CAPTURE_FIXTURES_PASS project_modules='+str(len(order))+' theorem_axioms='+str(len(axioms)))


if __name__ == '__main__':
    main()
