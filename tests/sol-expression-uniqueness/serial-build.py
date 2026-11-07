#!/usr/bin/env python3
"""Build import dependencies in topological order, one target per invocation."""
from pathlib import Path
import subprocess
import sys
root = Path.cwd()
seen = set()

def build(module):
    if module in seen:
        return
    seen.add(module)
    path = root / (module.replace('.', '/') + '.lean')
    if not path.is_file():
        return
    for line in path.read_text().splitlines():
        if line.startswith('import '):
            for dependency in line.split()[1:]:
                build(dependency)
    subprocess.run(['lake', 'build', '+'+module+':olean'], check=True)

for module in sys.argv[1:]:
    build(module)
