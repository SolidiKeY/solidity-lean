#!/usr/bin/env python3
"""Keep every fixed compiler spelling paired with a kernel-checked typed Lean row."""
import json,pathlib,sys
root=pathlib.Path(__file__).resolve().parents[2];folder=root/'tests/sol-numeric-literals'
cases=json.loads((folder/'spellings.json').read_text());rows=json.loads((folder/'lean-fixtures.json').read_text())
assert [(c['id'],c['mode'],c['spelling']) for c in cases]==[(r['id'],r['mode'],r['spelling']) for r in rows]
def string(s):return json.dumps(s,ensure_ascii=False)
def num(n):
 if n is None:return 'none'
 if n['tag']=='dec':return f"some (.dec {n['mantissa']} {n['fraction']} ({n['exponent']}))"
 assert n['tag']=='hex'
 ds='['+', '.join('⟨'+str(d)+', by decide⟩' for d in n['digits'])+']'
 return f"some (.hex {ds} {str(n['flag']).lower()})"
def yul(t):
 if t is None:return 'none'
 assert t['tag'] in ('dec','hex')
 return 'some (.yul'+('Dec' if t['tag']=='dec' else 'Hex')+' '+str(t['value'])+')'
casebody='def fixtureCases : List (String × String × String) := [\n'+',\n'.join('  ('+','.join(string(c[k]) for k in ['id','mode','spelling'])+')' for c in cases)+'\n]'
expected=[]
for r in rows:
 ns='['+', '.join(num(n)[5:] for n in r['numbers'])+']'
 expected.append('  ⟨'+', '.join([string(r['id']),string(r['mode']),string(r['spelling']),str(r['lexOk']).lower(),num(r['numeric']),ns,yul(r['yul'])])+'⟩')
body='def fixtureExpected : List FixtureObservation := [\n'+',\n'.join(expected)+'\n]\n\ntheorem fixture_observations_pass : fixtureObservations = fixtureExpected := by decide +kernel'
p=root/'Solidity/Frontend/NumericLiteralProofs/Fixtures.lean';original=p.read_text();wanted=original
for begin,end,content in [('-- BEGIN_FIXTURE_CASES','-- END_FIXTURE_CASES',casebody),('-- BEGIN_EXPECTED_FIXTURE_ROWS','-- END_EXPECTED_FIXTURE_ROWS',body)]:
 a=wanted.index(begin)+len(begin);b=wanted.index(end,a);wanted=wanted[:a]+'\n'+content+'\n'+wanted[b:]
if '--check' in sys.argv:assert original==wanted,'fixture Lean rows drifted'
else:p.write_text(wanted)
print(f'paired fixtures: {len(rows)} typed Lean rows, all spellings covered')
