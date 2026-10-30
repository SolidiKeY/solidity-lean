#!/usr/bin/env python3
"""Serial per-file diagnostics when Lean MCP is unavailable."""
import pathlib, subprocess, sys
files = sorted(pathlib.Path('Solidity/Storage/Representation').glob('*.lean'))
files += [pathlib.Path('tests/storage-values/Gap.lean'), pathlib.Path('Solidity.lean')]
for file in files:
    result = subprocess.run(['lake', '-f', 'lakefile.storage-values.toml', 'env', 'lean',
                             '--tstack=131072', '-j1', str(file)], capture_output=True, text=True)
    output = result.stdout + result.stderr
    if output:
        print(output, end='', flush=True)
    if result.returncode or 'warning:' in output or 'error:' in output:
        sys.exit('unclean diagnostics: ' + str(file))
    print('CLEAN ' + str(file), flush=True)
print(str(len(files)) + ' files passed', flush=True)
