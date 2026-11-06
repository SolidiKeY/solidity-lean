#!/usr/bin/env python3
"""Check frozen input identities, lane theorem axiom pins, inventories and scope.

Usage: audit.py [--scope-base REV] [AXIOM_LOG]

AXIOM_LOG is fresh Lean output containing the `#print axioms` reports of
`FullPins.lean` (for example a `lake build` log, which replays cached
messages) and must show FullPins being built or replayed.  Without it the
committed log named in `proof-source-identities.json` is used, and its SHA256
must equal the one recorded there next to the reviewed source hashes.  A
supplied log is not bound to the sources beyond that marker: record a fresh
one with `--record` (which rewrites the identities) to make it the committed
evidence.  The script reads only committed files, git and the optional log; it
does not run Lean.

Scope is checked against REV (default: the merge base of HEAD and
origin/master; the audit fails if neither resolves).  It covers the lane's
changes since that base only; the lane's earlier Codex history (from
`pins['base']`) was checked by the earlier audit on the Codex VM, whose
adoption commits are not published.  The shared generated files
`Solidity.lean` and `docs/module-map/frontend.md` may change only in lines
naming this lane's modules.
"""
import argparse, hashlib, json, pathlib, re, subprocess, sys
root = pathlib.Path(__file__).resolve().parents[3]
here = pathlib.Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument('--scope-base')
ap.add_argument('--record', action='store_true', help='copy AXIOM_LOG to the committed log and rewrite the identities')
ap.add_argument('axiom_log', nargs='?')
args = ap.parse_args()
pins = json.loads((here/'pins.json').read_text())
for name, expected in pins['inputs'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest() == expected, name
identities = json.loads((here/'proof-source-identities.json').read_text())
committed_log = root/identities['axiom_log']
if args.axiom_log is None:
    assert hashlib.sha256(committed_log.read_bytes()).hexdigest() == identities['axiom_log_sha256'], 'committed axiom log differs from its reviewed identity'
    log_path = committed_log
else:
    log_path = pathlib.Path(args.axiom_log)
log = log_path.read_text(errors='replace')
if args.axiom_log is not None:
    assert re.search(r'(Built|Replayed) Solidity\.Frontend\.LiteralGrammarH28\.FullPins\b', log) or 'LiteralGrammarH28/FullPins.lean:1:0' in log, 'supplied log shows no FullPins build'
found = {}
# A long axiom list wraps onto indented continuation lines; rejoin them.
lines = []
for raw in log.splitlines():
    if raw[:1].isspace() and lines:
        lines[-1] += ' ' + raw.strip()
    else:
        lines.append(raw)
for line in lines:
    if 'LiteralGrammarH28/FullPins.lean:' not in line:
        continue
    m = re.search(r"'Solidity\.Frontend\.LiteralGrammarH28\.([^']+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)", line)
    if not m:
        continue
    name, tail = m.groups()
    assert name not in found, ('duplicate axiom report', name)
    found[name] = [] if tail.startswith('does not') else re.split(r',\s*', tail.split('[', 1)[1][:-1])
assert found == pins['axioms'], ('axiom reports differ from pins', set(found) ^ set(pins['axioms']), [k for k in found if k in pins['axioms'] and found[k] != pins['axioms'][k]])
if args.record:
    assert args.axiom_log is not None, '--record needs AXIOM_LOG'
    kept = [l for l in lines if 'LiteralGrammarH28/FullPins.lean:' in l or 'LiteralGrammarH28/ProofSafety.lean:' in l]
    target = here/'evidence/axioms.log'
    target.write_text('\n'.join(kept) + '\n')
    identities = dict(sources={str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted((root/'Solidity/Frontend/LiteralGrammarH28').rglob('*.lean'))},
                      axiom_log=str(target.relative_to(root)),
                      axiom_log_sha256=hashlib.sha256(target.read_bytes()).hexdigest())
    (here/'proof-source-identities.json').write_text(json.dumps(identities, indent=2) + '\n')
controls = (root/'Solidity/Frontend/LiteralGrammarH28/HexControls.lean').read_text()
assert len(re.findall(r'\("(?:[^"\\]|\\.)*", (?:some|none)', controls)) == pins['hex_control_count']
body = (root/'Solidity/Frontend/LiteralGrammarH28/BodyControls.lean').read_text()
rows = []
for name, mode, raw, expected in re.findall(r'^  \("([^"\n]+)", (\.[^,]+), (\[[^\]]*\]), (none|some \[[^\]]*\])\)', body, re.M):
    rows.append(dict(id=name, mode=mode, raw=json.loads(raw), expected=None if expected == 'none' else json.loads(expected[5:])))
coverage = json.loads((root/'tests/h28-sol/literal-grammar/body-coverage.json').read_text())
assert rows == coverage and len(rows) == pins['body_control_count'], 'body coverage differs'
# Exclusive scope: lane paths plus this lane's module-map fragment and the
# combined file `fragments.sh` generates from it, and the generated root.
allowed = ('Solidity/Frontend/LiteralGrammarH28/', 'tests/h28-sol/literal-grammar/')
allowed_files = {'docs/feature-work/h28-literal-grammar.md',
                 'docs/module-map/frontend.d/literal-grammar.md', 'docs/module-map/frontend.md',
                 'Solidity.lean'}  # regenerated by register.sh
def owned_path(name):
    return name.startswith(allowed) or name in allowed_files
def rev_ok(rev):
    return subprocess.run(['git', 'rev-parse', '--verify', '-q', rev+'^{commit}'], cwd=root, capture_output=True).returncode == 0
scope_base = args.scope_base
if scope_base is None:
    assert rev_ok('origin/master'), 'no scope base: pass --scope-base or fetch origin/master'
    scope_base = subprocess.check_output(['git', 'merge-base', 'HEAD', 'origin/master'], cwd=root, text=True).strip()
assert rev_ok(scope_base), ('scope base does not resolve', scope_base)
paths = subprocess.check_output(['git', 'diff', '--no-renames', '--name-only', scope_base], cwd=root, text=True).splitlines()
paths += subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], cwd=root, text=True).splitlines()
bad = [name for name in paths if not owned_path(name)]
assert not bad, ('scope', bad)
for shared in ('Solidity.lean', 'docs/module-map/frontend.md'):
    diff = subprocess.check_output(['git', 'diff', '--no-renames', '-U0', scope_base, '--', shared], cwd=root, text=True).splitlines()
    changed = [l for l in diff if l[:1] in '+-' and not l.startswith(('+++', '---'))]
    assert all('LiteralGrammarH28' in l for l in changed), ('shared file changed outside lane lines', shared, changed)
scope_checked = len(paths)
for source in (root/'Solidity/Frontend/LiteralGrammarH28').rglob('*.lean'):
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|unsafe|native_decide|maxHeartbeats)\b', text), source
    assert not re.search(r'^\s*axiom\b', text, re.M), source
inventory = json.loads((root/'tests/h28-sol/literal-grammar/theorem-inventory.json').read_text())
assert set(found) == set(inventory['public_theorems'])
assert all(set(v) <= {'propext', 'Quot.sound', 'Classical.choice'} for v in found.values())
manifest = json.loads((root/'tests/h28-sol/literal-grammar/registration.json').read_text())
assert {v['module'] for v in manifest['modules']} == {str(p.relative_to(root))[:-5].replace('/', '.') for p in (root/'Solidity/Frontend/LiteralGrammarH28').rglob('*.lean')}
safety = json.loads((root/'tests/h28-sol/literal-grammar/evidence/proof-safety-diag.json').read_text())
assert safety['success'] and not safety['timed_out'] and not safety['partial']
assert sorted(i['message'] for i in safety['items'] if i['message'].startswith('DECL_SAFETY ')) == pins['safe_declarations']
fresh_safety = sorted(re.search(r'(DECL_SAFETY .*)', l).group(1) for l in lines if 'LiteralGrammarH28/ProofSafety.lean:' in l and 'DECL_SAFETY ' in l)
if fresh_safety:
    assert fresh_safety == pins['safe_declarations'], ('fresh proof-tactic safety report differs', fresh_safety)
assert len(pins['safe_declarations']) == 8 and all(x.endswith('Lean.DefinitionSafety.safe') for x in pins['safe_declarations'])
assert len(json.loads((root/'tests/h28-sol/literal-grammar/full-coverage.json').read_text())) == pins['full_control_count']
boundary = json.loads((root/'tests/h28-sol/literal-grammar/boundary-coverage.json').read_text())
assert sum(len(v) for v in boundary.values()) == pins['boundary_control_count']
# Compare the public-theorem pin set to the actual source, not only another manifest.
actual_theorems = [n for p in (root/'Solidity/Frontend/LiteralGrammarH28').rglob('*.lean') for n in re.findall(r'^theorem\s+([\w.]+)', p.read_text(), re.M)]
assert len(actual_theorems) == len(set(actual_theorems)) and set(actual_theorems) == set(found)
constructors = json.loads((root/'tests/h28-sol/literal-grammar/constructor-inventory.json').read_text())
actual_inductives = {p.stem+'.'+n for p in (root/'Solidity/Frontend/LiteralGrammarH28').rglob('*.lean') for n in re.findall(r'^inductive\s+([\w]+)', p.read_text(), re.M)}
assert actual_inductives == set(constructors), ('inductive inventory differs', actual_inductives, set(constructors))
for key, expected in constructors.items():
    module, name = key.split('.')
    source = (root/('Solidity/Frontend/LiteralGrammarH28/'+module+'.lean')).read_text()
    block = source.split('inductive '+name, 1)[1].split('where', 1)[1].split('\n\n', 1)[0]
    actual = re.findall(r'(?:^|\|)\s*([A-Za-z][A-Za-z0-9_]*)', block)
    assert actual == expected, (key, actual, expected)
full_source = (root/'Solidity/Frontend/LiteralGrammarH28/FullControls.lean').read_text()
full_rows = [dict(id=name, mode=mode, raw=json.loads(raw), expected=expected) for name,mode,raw,expected in re.findall(r'^  \("([^"\n]+)", (\.[^,]+), (\[[^\]]*\]), (.+)\)[,\]]', full_source, re.M)]
assert full_rows == json.loads((root/'tests/h28-sol/literal-grammar/full-coverage.json').read_text()), 'exact full coverage differs'
import ast
boundary_source = (root/'Solidity/Frontend/LiteralGrammarH28/BoundaryControls.lean').read_text()
for group, definition in [('quote','quoteControls'),('scan','scanControls'),('plain','plainControls')]:
    block = boundary_source.split('def '+definition,1)[1].split(':= [',1)[1].split(']\n',1)[0]
    actual=[]
    for line in block.splitlines():
        if not line.startswith('  ('): continue
        row = line.strip().rstrip(',').removesuffix(']').removesuffix(')')
        row = row[1:]
        row = re.sub(r'\bnone\b','None',row)
        row = re.sub(r'\bsome\s+','',row)
        item=ast.literal_eval('('+row+')')
        if group=='scan': name,q,raw,expected=item; value=dict(id=name,q=q,raw=raw,expected=expected)
        else: name,raw,expected=item; value=dict(id=name,raw=raw,expected=expected)
        # JSON represents tuple values as arrays.
        actual.append(json.loads(json.dumps(value)))
    assert actual == boundary[group], ('exact boundary coverage differs', group, actual, boundary[group])
assert identities['sources'] == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in (root/'Solidity/Frontend/LiteralGrammarH28').rglob('*.lean')}, 'reviewed proof sources changed'
hexrows = [dict(raw=json.loads('"'+raw+'"'), expected=None if expected=='none' else json.loads(expected[5:])) for raw,expected in re.findall(r'\("((?:[^"\\]|\\.)*)", (none|some \[[^\]]*\])\)', controls)]
assert hexrows == json.loads((root/'tests/h28-sol/literal-grammar/hex-coverage.json').read_text())
fixtures = json.loads((root/'tests/h28-sol/literal-grammar/solc-cases.json').read_text())
n_cases = len(fixtures["cases"])
assert n_cases == 71 and len({c["id"] for c in fixtures["cases"]}) == n_cases
by_id = {row['id']: row for row in full_rows}
assert len(by_id) == len(full_rows)
for case in fixtures['cases']:
    if case['lexemeKind'] == 'fragment-sequence':
        assert case['checkedModelAccept'] and len(case['fragmentSpellings']) == len(case['fragmentHex'])
        assert case['spelling'] == ' '.join(case['fragmentSpellings']), case['id']
        assert ''.join(case['fragmentHex']) == case['checkedModelHex']
        pieces=list(zip(case['fragmentSpellings'],case['fragmentHex']))
    else: pieces=[(case['spelling'],case['checkedModelHex'])]
    for index,(spelling,hexvalue) in enumerate(pieces):
        key=case['id'] if case['lexemeKind']=='single' else case['id']+'#'+str(index)
        row=by_id[key]
        assert row['raw'] == list(spelling.encode('utf-8')), key
        assert row['mode'] == { 'sol':'.sol', 'asm':'.asm', 'yul':'.yul 7'}[case['mode']], key
        if not case['checkedModelAccept']: expected='none'
        else:
            tag={'plain':'str','hex':'hexStr','unicode':'unicodeStr'}[case['checkedModelFlavor']]
            expected='some (.tok (.'+tag+' '+str(list(bytes.fromhex(hexvalue)))+'))'
        assert row['expected'] == expected, (key,row['expected'],expected)
    if case['compilerAccept'] != case['checkedModelAccept']: assert case.get('difference')
observations=json.loads((root/'tests/h28-sol/literal-grammar/solc-observations.json').read_text())
assert not observations['failures'] and len(observations["observations"]) == 2 * n_cases
assert {(row['id'],row['viaIR']) for row in observations['observations']} == {(c['id'],v) for c in fixtures['cases'] for v in [False,True]}
print(f"PASS: {len(pins['inputs'])} frozen input hashes; {len(found)} exact theorem axiom sets; {sum(pins[k] for k in ('hex_control_count','body_control_count','boundary_control_count','full_control_count'))} kernel control rows; 8 safe proof-tactic declarations ({'fresh' if fresh_safety else 'committed'} report); exact local registration; exclusive scope ({scope_checked} changed paths since {scope_base}); trust restrictions; axiom log {log_path}")
