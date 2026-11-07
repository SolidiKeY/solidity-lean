#!/usr/bin/env python3
"""Render a source-pinned V07 subset probe using the existing generic inspector.

Guarded regression: source-only binder guesses must not be called elaborated
signatures, and a live subset must not silently replace the frozen full census.
This tool reuses the bytecode audit's unchanged Lean template; all bulk output
stays external. The probe is inspection only, not feasibility or acceptance.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import subprocess

TEMPLATE_PATH = 'scripts/h62/item2/audit-bytecode-selection/elaborated_census.py'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def render(repo, inventory, output, modules):
    repo, output = repo.resolve(), output.resolve()
    if output == repo or repo in output.parents:
        raise ValueError('external output directory required')
    if output.exists():
        raise FileExistsError('existing destination refused')
    receipt = json.loads((repo/'tests/h62/item2/audit-v07-lowering/frozen-reproduction.json').read_text())
    raw = inventory.read_bytes()
    if sha(raw) != receipt['artifacts']['source-inventory.json']:
        raise ValueError('frozen inventory hash mismatch')
    ledger = json.loads(raw)
    available = {r['path'][:-5].replace('/', '.'): r for r in ledger['modules']}
    if not modules or len(set(modules)) != len(modules) or not set(modules) <= available.keys():
        raise ValueError('nonempty distinct mapped modules required')
    modules = sorted(modules)
    sources = {}
    for module in modules:
        row = available[module]
        current = (repo/row['path']).read_bytes()
        frozen = subprocess.check_output(['git', '-C', str(repo), 'show', receipt['base']+':'+row['path']])
        if current != frozen or sha(current) != row['sha256']:
            raise ValueError('module differs from frozen bytes: '+module)
        sources[row['path']] = sha(current)
    template_raw = (repo/TEMPLATE_PATH).read_bytes()
    assignments = [node for node in ast.parse(template_raw).body if isinstance(node, ast.Assign)
                   and any(isinstance(target, ast.Name) and target.id == 'TEMPLATE' for target in node.targets)]
    if len(assignments) != 1:
        raise ValueError('generic inspection template missing or ambiguous')
    template = ast.literal_eval(assignments[0].value)
    if not isinstance(template, str):
        raise ValueError('generic inspection template is not literal text')
    pins = dict(base=receipt['base'], modules=modules, source_sha256=sources,
                inspection_template_sha256=sha(template.encode()))
    fingerprint = sha(json.dumps(pins, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode())
    probe = ('import Lean\n'+''.join('import '+m+'\n' for m in modules)+
             template.replace('MODULES', ', '.join('`'+m for m in modules)).replace('FINGERPRINT', fingerprint))
    pins.update(manifest_sha256=fingerprint, inspection_sha256=sha(probe.encode()),
                template_provider=TEMPLATE_PATH, template_provider_sha256=sha(template_raw),
                inventory_sha256=sha(raw),
                boundary='Live environment inspection of a frozen-source subset; not full telescope census, feasibility or original migration acceptance.')
    output.mkdir(parents=True)
    (output/'Probe.lean').write_text(probe)
    (output/'pins.json').write_text(json.dumps(pins, indent=2)+'\n')
    return pins


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--inventory', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--module', action='append', required=True)
    args = parser.parse_args()
    print(json.dumps(render(args.repo, args.inventory, args.output, args.module), indent=2))
