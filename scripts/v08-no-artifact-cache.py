#!/usr/bin/env python3
"""Run the existing bounded gate with Lake optional artifact caching disabled.
The warm package build directory, budgets and all other runner code are unchanged.
"""
import ast, os, sys
from pathlib import Path

runner = Path(__file__).with_name('v08-bounded.py')
source = runner.read_text()
old = "'-e', 'LAKE_CACHE_DIR=/workspace/.setup/cache/lake',"
new = "'-e', 'LAKE_CACHE_DIR=', '-e', 'LAKE_ARTIFACT_CACHE=false',"
assert source.count(old) == 1, 'runner cache override changed; inspect before use'
source = source.replace(old, new)
old_assert = "script += 'lean --version; lake --version; '"
new_assert = "script += 'test \"$LAKE_CACHE_DIR\" = \"\"; test \"$LAKE_ARTIFACT_CACHE\" = false; echo V08_OPTIONAL_ARTIFACT_CACHE_DISABLED; lean --version; lake --version; '"
assert source.count(old_assert) == 1
source = source.replace(old_assert, new_assert)
ast.parse(source)
if sys.argv[1:] == ['--self-test']:
 assert "'--memory', '12g'" in source and 'wall_limit_seconds = 600' in source
 assert "'-e', 'LEAN_NUM_THREADS=1'" in source
 assert new in source and old not in source
 print('PASS: exact two replacements; Docker cache variables and inner assertions; original budgets retained')
else:
 os.environ['LAKE_CACHE_DIR'] = ''
 os.environ['LAKE_ARTIFACT_CACHE'] = 'false'
 exec(compile(source, str(runner), 'exec'), {'__name__': '__main__', '__file__': str(runner)})
