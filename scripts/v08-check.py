#!/usr/bin/env python3
"""Check the V08 proof inventory, core import closure and append-only registration.
Supply a successful v08-bounded.py JSON result. Does not run Lean or modify pins.
"""
import hashlib, json, re, subprocess, sys
from pathlib import Path
root = Path(__file__).resolve().parent.parent
result = json.loads(Path(sys.argv[1]).read_text())
assert result['exit'] == 0 and not result['resource_or_time_guard_stopped']
assert result['samples'] > 0 and result['peak_sampled_aggregate_rss_bytes'] > 0
assert result['cgroup_peak_bytes'] is not None
assert result['source_unchanged']
for path, digest in result['source_sha256'].items():
 assert hashlib.sha256((root/path).read_bytes()).hexdigest() == digest, ('stale source evidence', path)
current_paths = set(subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard', '*.lean', 'lakefile.toml', 'scripts/v08-runtime.toml'], cwd=root).decode().split('\0')) - {''}
assert current_paths == set(result['source_sha256']), 'source inventory changed'
subprocess.run(['git','merge-base','--is-ancestor',result['git_head_at_check'],'HEAD'],cwd=root,check=True)
assert hashlib.sha256(Path(result['log']).read_bytes()).hexdigest() == result['log_sha256']
log = Path(result['log']).read_text()
assert not re.search(r'^error:', log, re.MULTILINE)
expected = json.loads((root / 'scripts/v08-axiom-pins.json').read_text())
found = {}
for name, axes in re.findall(r"'(Solidity\.Lowering\.V08\.[^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log):
 actual = sorted(x.strip() for x in axes.split(',') if x.strip())
 assert set(actual) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, actual)
 if name in found: assert found[name] == actual
 found[name] = actual
assert found == expected, ('axiom inventory mismatch', set(expected)-set(found), set(found)-set(expected))
theorems = set()
for path in (root / 'Solidity/Lowering/V08').glob('*.lean'):
 source = path.read_text()
 namespace = re.search(r'^namespace ([A-Za-z0-9_.]+)', source, re.MULTILINE)
 if namespace:
  theorems.update(namespace.group(1) + '.' + name for name in re.findall(r'^theorem ([A-Za-z0-9_]+)', source, re.MULTILINE))
assert theorems == set(expected), ('unprinted or obsolete theorem pin', theorems ^ set(expected))
core = ['Callable', 'AbiObservations', 'Transactions', 'LibraryCreation', 'CallableMetadata', 'EnvironmentProjection', 'SelectorObservations', 'CryptoObservations']
seen = set()
def visit(module):
 if module in seen: return
 seen.add(module)
 # Match the repository's source-elaborator boundary. AST's existing import
 # of built-in Lean is preserved; no external package dependency is introduced.
 forbidden = re.match(r'^Solidity\.(?:Tools\.SolCases$|Syntax\.(?:Elab|Quote|Splice)(?:\.|$)|Calculus\.(?:Print[^.]*|Surface[^.]*|TacticSyntax|Quote|NamedTerm)(?:\.|$)|Frontend\.)', module)
 assert not forbidden, ('owned core reaches source elaborator', module)
 path = root / (module.replace('.', '/') + '.lean')
 if path.exists():
  for line in path.read_text().splitlines():
   if line.startswith('import '):
    for dependency in line[7:].split():
     if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', dependency): visit(dependency)
for module in core: visit('Solidity.Lowering.V08.' + module)
base = 'fb379ae20f10e2c92113453ddd9d40d8f2efbe09'
for path in ['Solidity.lean', 'docs/module-map.md', 'docs/README.md']:
 original = subprocess.check_output(['git', 'show', base+':'+path], cwd=root)
 assert (root/path).read_bytes().startswith(original), ('not append-only', path)
paths = subprocess.check_output(['git', 'diff', '--name-only', base], cwd=root, text=True).splitlines()
untracked = subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=root,text=True).splitlines()
paths = sorted(set(paths + untracked))
for path in paths:
 if path == 'lakefile.v08-runtime.toml' and path in untracked:
  old_control = (root/'lakefile.toml').read_text().replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]')
  assert (root/path).read_text() == old_control, 'unexpected legacy generated control'
  continue
 assert path.startswith(('Solidity/Lowering/V08/', 'scripts/v08-')) or path in ['Solidity.lean','docs/module-map.md','docs/README.md','docs/feature-work/roadmap-v08-world-lowering.md'], ('ownership', path)
doc = root/'docs/feature-work/roadmap-v08-world-lowering.md'
for link in re.findall(r'\]\(([^)#]+)(?:#[^)]*)?\)', doc.read_text()):
 if not link.startswith(('http:', 'https:')): assert (doc.parent/link).exists(), ('broken owned link', link)
print('PASS:', len(theorems), 'exact theorem axiom pins;', len(seen), 'modules in owned core closure; append-only registration, scope and owned links')
