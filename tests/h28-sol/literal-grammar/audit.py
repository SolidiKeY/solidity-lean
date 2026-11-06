#!/usr/bin/env python3
"""Check frozen input identities, lane theorem axiom pins and scope.
The supplied log must be actual Lean output; this script does not run Lean.
"""
import argparse, hashlib, json, pathlib, re, subprocess
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('axiom_log', type=pathlib.Path)
parser.add_argument('--evidence-dir', type=pathlib.Path,
                    help='H44 external evidence directory (no files are copied into git)')
parser.add_argument('--published-integration', action='store_true',
                    help='audit the explicitly adopted e8247d927 integration baseline')
args = parser.parse_args()
root = pathlib.Path(__file__).resolve().parents[3]
evidence_dir = args.evidence_dir or root/'tests/h28-sol/literal-grammar/evidence'
# This is a fixed human-published adoption, never a mutable origin/master exemption.
integration = 'e8247d9277190b71488387dac594e82b2b191942' if args.published_integration else None
if integration:
    subprocess.run(['git', 'merge-base', '--is-ancestor', integration, 'HEAD'], cwd=root, check=True)
pins = json.loads((pathlib.Path(__file__).with_name('pins.json')).read_text())
for name, expected in pins['inputs'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest() == expected, name
log = args.axiom_log.read_text()
found = {}
for name, tail in re.findall(r"'Solidity\.Frontend\.LiteralGrammarH28\.([^']+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)", log):
    assert name not in found, ('duplicate axiom report', name)
    found[name] = [] if tail.startswith('does not') else re.split(r',\s*', tail.split('[', 1)[1][:-1])
assert found == pins['axioms'], (found, pins['axioms'])
controls = (root/'Solidity/Frontend/LiteralGrammarH28/HexControls.lean').read_text()
assert len(re.findall(r'\("(?:[^"\\]|\\.)*", (?:some|none)', controls)) == pins['hex_control_count']
body = (root/'Solidity/Frontend/LiteralGrammarH28/BodyControls.lean').read_text()
rows = []
for name, mode, raw, expected in re.findall(r'^  \("([^"\n]+)", (\.[^,]+), (\[[^\]]*\]), (none|some \[[^\]]*\])\)', body, re.M):
    rows.append(dict(id=name, mode=mode, raw=json.loads(raw), expected=None if expected == 'none' else json.loads(expected[5:])))
coverage = json.loads((root/'tests/h28-sol/literal-grammar/body-coverage.json').read_text())
assert rows == coverage and len(rows) == pins['body_control_count'], 'body coverage differs'
# Verify every explicitly authorized adoption; frozen proof/input pins stay original.
allowed = ('Solidity/Frontend/LiteralGrammarH28/', 'tests/h28-sol/literal-grammar/')
def owned_path(name):
    return name.startswith(allowed) or name == 'docs/feature-work/h28-literal-grammar.md'
scope_base = pins['base']
adoption_path = root/'tests/h28-sol/literal-grammar/adopted-master.json'
if adoption_path.is_file():
    adoption = json.loads(adoption_path.read_text())
    assert adoption['original_base'] == pins['base']
    chain = adoption['previous_adoptions'] + [dict(published_master=adoption['published_master'], preserved_owned_head=adoption['preserved_owned_head'])]
    assert chain == [
        dict(published_master='8495f1deb0a95dd6b9301822d8649ab76b217681', preserved_owned_head='0858098f1f278d99ca2d1b8f19100cef441f7cb0'),
        dict(published_master='f77cf60d3cea8f7f1db8db29cc027532b0cd3fce', preserved_owned_head='9cbd923a5f082d2d2513f23742ffd4e1009e009b'),
        dict(published_master='9584f9e7df09f638d9e0cb8930501d1660aa4b2f', preserved_owned_head='405995c18292657b8797521bbc716a202bc151f2'),
        dict(published_master='b86ae4568cef6d6226f4d170360bbb089debe3fb', preserved_owned_head='59c3e31c820830d179a1b24911dcf8f3f6b001af')]
    for entry in chain:
        published, preserved = entry['published_master'], entry['preserved_owned_head']
        for earlier, later in [(scope_base, preserved), (scope_base, published)] + ([] if integration else [(preserved, 'HEAD')]):
            subprocess.run(['git', 'merge-base', '--is-ancestor', earlier, later], cwd=root, check=True)
        if subprocess.run(['git', 'merge-base', '--is-ancestor', published, 'HEAD'], cwd=root).returncode:
            # Only this exact latest merge may be validated before its commit.
            assert entry == chain[-1]
            assert subprocess.check_output(['git', 'rev-parse', 'MERGE_HEAD'], cwd=root, text=True).strip() == published
        prior_paths = subprocess.check_output(['git', 'diff', '--name-only', scope_base, preserved], cwd=root, text=True).splitlines()
        assert all(owned_path(name) for name in prior_paths), 'pre-adoption ownership violation'
        scope_base = published
# Published integration may rebase prior owned history. The historical ownership
# checks above remain, and all 24 reviewed proof hashes below must still match.
if integration:
    scope_base = integration
paths = subprocess.check_output(['git', 'diff', '--name-only', scope_base], cwd=root, text=True).splitlines()
paths += subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], cwd=root, text=True).splitlines()
allowed = ('Solidity/Frontend/LiteralGrammarH28/', 'tests/h28-sol/literal-grammar/')
for name in paths:
    assert name.startswith(allowed) or name == 'docs/feature-work/h28-literal-grammar.md', ('scope', name)
for source in (root/'Solidity/Frontend/LiteralGrammarH28').rglob('*.lean'):
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|unsafe|native_decide|maxHeartbeats)\b', text), source
    assert not re.search(r'^\s*axiom\b', text, re.M), source
inventory = json.loads((root/'tests/h28-sol/literal-grammar/theorem-inventory.json').read_text())
assert set(found) == set(inventory['public_theorems'])
assert all(set(v) <= {'propext', 'Quot.sound', 'Classical.choice'} for v in found.values())
manifest = json.loads((root/'tests/h28-sol/literal-grammar/registration.json').read_text())
assert {v['module'] for v in manifest['modules']} == {str(p.relative_to(root))[:-5].replace('/', '.') for p in (root/'Solidity/Frontend/LiteralGrammarH28').rglob('*.lean')}
safety = json.loads((evidence_dir/'proof-safety-diag.json').read_text())
assert safety['success'] and not safety['timed_out'] and not safety['partial']
assert sorted(i['message'] for i in safety['items'] if i['message'].startswith('DECL_SAFETY ')) == pins['safe_declarations']
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
identities = json.loads((root/'tests/h28-sol/literal-grammar/proof-source-identities.json').read_text())
assert identities['sources'] == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in (root/'Solidity/Frontend/LiteralGrammarH28').rglob('*.lean')}, 'reviewed proof sources changed'
assert hashlib.sha256(args.axiom_log.read_bytes()).hexdigest() == identities['axiom_log_sha256'], 'axiom report does not match reviewed source evidence'
hexrows = [dict(raw=json.loads('"'+raw+'"'), expected=None if expected=='none' else json.loads(expected[5:])) for raw,expected in re.findall(r'\("((?:[^"\\]|\\.)*)", (none|some \[[^\]]*\])\)', controls)]
assert hexrows == json.loads((root/'tests/h28-sol/literal-grammar/hex-coverage.json').read_text())
fixtures = json.loads((root/'tests/h28-sol/literal-grammar/solc-cases.json').read_text())
assert len(fixtures['cases']) == 58 and len({c['id'] for c in fixtures['cases']}) == 58
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
assert not observations['failures'] and len(observations['observations']) == 116
assert {(row['id'],row['viaIR']) for row in observations['observations']} == {(c['id'],v) for c in fixtures['cases'] for v in [False,True]}
print(f"PASS: {len(pins['inputs'])} frozen input hashes; {len(found)} exact theorem axiom sets; 242 kernel control rows; 8 safe proof-tactic declarations; exact local registration; exclusive scope; trust restrictions (historical log bound to unchanged sources, not a fresh Lean run)")
