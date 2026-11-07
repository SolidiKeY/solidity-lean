#!/usr/bin/env python3
"""Guard cached evaluator arity drift from falsely validating encoding failure.

Run under the audit bounded runner (which owns the writer lock). Compile exact
current capture leaves and this actual fixture into a private library. Remaining
project/SDK dependencies are cached inputs, not independently source certified.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
LEAN = Path('/workspace/.setup/tools/lean-4.24.0-linux/bin/lean')
LEAVES = ['Solidity/Source/Hoare.lean',
          'Solidity/Lowering/Readonly/CapturePhases.lean',
          'Solidity/Lowering/Readonly/CaptureFailures.lean']
FIXTURE = 'tests/h62/item1/readonly-bind/EncodingFailureControls.lean'
PREFIX = 'Solidity.H62.ReadonlyBind.EncodingFailureControls.'
THEOREMS = ['signature', 'allocated', 'joint_capture', 'encoding_failure']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_hashes(pins):
    for path, digest in pins.items():
        if sha(Path(path)) != digest:
            raise ValueError('protected input or artifact changed: '+str(path))


def parse_axioms(log):
    records = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", log)
    if len(records) != len(THEOREMS) or {n for n, _ in records} != {PREFIX+n for n in THEOREMS}:
        raise ValueError('missing or ambiguous axiom records')
    axioms = {name: [a.strip() for a in raw.split(',') if a.strip()]
              for name, raw in records}
    if any(set(values)-ALLOWED for values in axioms.values()):
        raise ValueError('unexpected theorem axiom')
    return axioms


def compile_staged(original, staged, artifact, run):
    raw = original.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    staged.parent.mkdir(parents=True, exist_ok=True)
    staged.write_bytes(raw)
    staged.chmod(0o444)
    verify_hashes({str(original): digest, str(staged): digest})
    run(staged, artifact)
    verify_hashes({str(original): digest, str(staged): digest})
    return {'source_sha256': digest, 'artifact_sha256': sha(artifact)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    library = out/'library'
    library.mkdir()
    cache = ROOT/'.lake/build/lib/lean'
    excluded = [p[:-5] for p in LEAVES]
    for path in sorted((cache/'Solidity').rglob('*')):
        if not path.is_file():
            continue
        relative = path.relative_to(cache).as_posix()
        if any(relative.startswith(name+'.') for name in excluded):
            continue
        dest = library/relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.symlink_to(path.resolve())
    env = dict(os.environ, LEAN_PATH=str(library))
    steps = []
    sources = {}
    protected = {}
    pins = {str(p): sha(p) for p in [LEAN, ROOT/'lean-toolchain', Path(__file__).resolve()]}
    version = subprocess.check_output([str(LEAN), '--version'], text=True).strip()

    def run(tag, source, artifact=None):
        command = [str(LEAN), '-j1', '--tstack=131072', '--root='+str(out)]
        if artifact:
            artifact.parent.mkdir(parents=True, exist_ok=True)
            command += ['-o', str(artifact)]
        command.append(str(source))
        log = out/(tag+'.log')
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=ROOT, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        raw = log.read_bytes()
        steps.append({'command': command, 'exit': result.returncode,
                      'log': str(log), 'sha256': hashlib.sha256(raw).hexdigest()})
        if result.returncode:
            raise SystemExit('ENCODING_FIXTURE_FAIL '+str(log))
        return raw.decode()

    for relative in LEAVES+[FIXTURE]:
        source = out/(relative if relative in LEAVES else 'EncodingFailureControls.lean')
        artifact = library/(relative[:-5]+'.olean' if relative in LEAVES
                            else 'EncodingFailureControls.olean')
        record = compile_staged(ROOT/relative, source, artifact,
                                lambda staged, obj: run(Path(relative).stem, staged, obj))
        protected[str(source)] = record['source_sha256']
        protected[str(artifact)] = record['artifact_sha256']
        sources[relative] = record
    probe = out/'Probe.lean'
    probe.write_text('import EncodingFailureControls\n'+''.join(
        '#print axioms '+PREFIX+name+'\n' for name in THEOREMS))
    protected[str(probe)] = sha(probe)
    log = run('axioms', probe)
    axioms = parse_axioms(log)
    for relative, record in sources.items():
        if sha(ROOT/relative) != record['source_sha256']:
            raise ValueError('current source changed during check')
    verify_hashes({**pins, **protected})
    verify_hashes({step['log']: step['sha256'] for step in steps})
    receipt = {'boundary': __doc__, 'protected_sha256': protected,
               'input_pins': pins, 'sources': sources, 'steps': steps,
               'axioms': axioms, 'compiler_sha256': sha(LEAN),
               'compiler_version': version,
               'toolchain_sha256': sha(ROOT/'lean-toolchain'),
               'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()}
    (out/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print('ENCODING_FIXTURE_PASS '+str(out/'receipt.json'))


if __name__ == '__main__':
    main()
