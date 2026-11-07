#!/usr/bin/env python3
"""Generate a small disposable Lean driver; bulk output stays off Git."""
import argparse
import json
from pathlib import Path
from census import generate

ap = argparse.ArgumentParser()
ap.add_argument('--root', type=Path, default=Path.cwd())
ap.add_argument('--driver', type=Path, required=True)
ap.add_argument('--output', type=Path, required=True)
a = ap.parse_args()
census = generate(a.root)
modules = [r['module'][:-5].replace('/', '.') for r in census['modules']]
imports = '\n'.join('import '+m for m in modules)
a.output.mkdir(parents=True, exist_ok=True)
commands = []
for module in modules:
    target = a.output.resolve() / (module + '.json')
    commands.append('set_option pp.all true in\n#audit_census ' + json.dumps(str(target)) + ' modules ' + json.dumps(module))
a.driver.write_text(imports+'\nimport tests.h62.item2.«audit-compiler-transport».Reflect\n'+ '\n'.join(commands) + '\n')
print(f'Generated driver for {len(modules)} frozen modules: {a.driver}')
