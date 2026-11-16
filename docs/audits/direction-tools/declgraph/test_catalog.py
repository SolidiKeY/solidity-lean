#!/usr/bin/env python3
"""Regression checks for explicit action-step boundaries."""
import pathlib,runpy
API=runpy.run_path(str(pathlib.Path(__file__).with_name('catalog.py')))
for source,index in [('      - uses: leanprover/lean-action@v1\n        with:\n          build: false',0),('      - name: Setup\n        uses: leanprover/lean-action@v1\n        with:\n          test: false',1)]:
 assert API['action_step_indent'](source.splitlines(),index)==6
assert API['action_settings'](['        with:', '          test: false', '        env:', '          SAMPLE: true', '        working-directory: code'])=={'test':'false'}
assert all('env' not in a['settings'] for a in API['build']()['lean_actions'])
assert any(a['settings'].get('build')=='false' for a in API['build']()['lean_actions'])
assert any(a['settings'].get('build-args')=='Solidity.Tools.DirectRuntime' for a in API['build']()['lean_actions'])
print('CATALOG_FIXTURES_PASS direct_and_named_steps explicit_settings')
