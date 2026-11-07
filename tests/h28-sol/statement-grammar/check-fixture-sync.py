#!/usr/bin/env python3
"""Read-only synchronization check: source bytes, manifest, Lean cases/imports."""
import hashlib,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parents[3]
HERE=ROOT/'tests/h28-sol/statement-grammar/fixtures'
MOD=ROOT/'Solidity/Frontend/StatementGrammarH28'
spec=json.loads((HERE/'manifest.json').read_text())
assert len(spec['cases'])==45 and len(spec['requiredCtors'])==40
assert len(set(spec['requiredCtors']))==40
assert len(set(c['id'] for c in spec['cases']))==45
assert {p.name for p in HERE.iterdir()}=={'manifest.json'}|{c['file'] for c in spec['cases']}
data=(MOD/'FixtureData.lean').read_text()
pattern=r'def statementFixture(\d+) : StatementFixture :=\s*⟨("(?:[^"\\]|\\.)*"), (true|false), (true|false), \[(.*?)\]⟩'
found=re.findall(pattern,data,re.S);assert len(found)==45,len(found)
for i,(num,source,accepted,profile,ctors) in enumerate(found):
 c=spec['cases'][i];assert int(num)==i
 content=(HERE/c['file']).read_text();assert json.loads(source)==content,c['id']
 assert hashlib.sha256(content.encode()).hexdigest()==c['sha256'],c['id']
 assert (accepted=='true')==c['leanAccept'] and (profile=='true')==c['profile'],c['id']
 assert re.findall(r'\.([A-Za-z0-9_]+)',ctors)==c['ctors'],c['id']
 case=(MOD/'FixtureControls'/('Case'+str(i).zfill(2)+'.lean')).read_text()
 expected='theorem statementFixture'+str(i)+'_checked : statementFixtureCheck statementFixture'+str(i)+' = true := by decide +kernel'
 expected_file='import Solidity.Frontend.StatementGrammarH28.FixtureData\n\nnamespace Solidity.Frontend.StatementGrammarH28\n'+expected+'\n#print axioms statementFixture'+str(i)+'_checked\nend Solidity.Frontend.StatementGrammarH28\n'
 assert case==expected_file,c['id']
listed=re.search(r'def statementFixtures : List StatementFixture := \[(.*?)\]',data,re.S).group(1)
assert list(map(int,re.findall(r'statementFixture(\d+)',listed)))==list(range(45))
imports=re.findall(r'^import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case(\d+)$',(MOD/'ConstructorControls.lean').read_text(),re.M)
assert sorted(map(int,imports))==list(range(45))
required=re.search(r'def requiredStatementCtors : List Ctor := \[(.*?)\]',data,re.S).group(1)
assert re.findall(r'\.([A-Za-z0-9_]+)',required)==spec['requiredCtors']
assert set(spec['requiredCtors'])<=set(x for c in spec['cases'] if c['leanAccept'] for x in c['ctors'])
print('PASS: 45 source/Lean/manifest cases, all imports, and 40 constructor obligations synchronized')
