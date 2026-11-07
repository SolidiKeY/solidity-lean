#!/usr/bin/env python3
"""Exact paired observations, retaining every lexical/compiler stage difference."""
import fractions,json,pathlib,re,sys
folder=pathlib.Path(__file__).resolve().parent

def number(n):
 if n['tag']=='hex':
  value=0
  for d in n['digits']:
   assert 0<=d<16
   value=16*value+d
  return fractions.Fraction(value)
 assert n['tag']=='dec'
 m,f,e=n['mantissa'],n['fraction'],n['exponent']
 return fractions.Fraction(m*10**max(e,0),10**(f+max(-e,0)))

def ratio(q):return dict(numerator=q.numerator,denominator=q.denominator)

def compute():
 lean=json.loads((folder/'evidence/lean-fixtures.actual.json').read_text())
 pinned=json.loads((folder/'lean-fixtures.json').read_text())
 assert lean==pinned,'fresh Lean fixture observations differ'
 solc=json.loads((folder/'solc-0.8.38.json').read_text())
 assert solc['version']=='0.8.38+commit.1835d247.Emscripten.clang'
 assert [r['id'] for r in lean]==[r['id'] for r in solc['results']]
 notes={
 'S07':'The fragment is a numeric token followed by a period; the compiler rejects the expression context.',
 'S18':'The fragment is an identifier; the compiler rejects an undeclared name.',
 'S31':'The number and elementary type are separately lexed; the compiler rejects the expression context.',
 'Y06':'The Yul fragment tokenizes as period plus integer; raw yulNumber refuses .1 and the compiler rejects it.',
 'S33':'The hex token retains a false deterministic checksum flag; the compiler diagnoses its checksum.'}
 result=[]
 for l,s in zip(lean,solc['results']):
  assert (l['id'],l['mode'],l['spelling'])==(s['id'],s['mode'],s['spelling'])
  values=[number(n) for n in l['numbers']]
  if l['mode']=='yul' and l['yul'] is not None:
   assert l['yul']['tag'] in ('dec','hex')
   values=[fractions.Fraction(l['yul']['value'])]
  compiler=[]
  if s['accepted']:
   assert l['lexOk'],'compiler accepted but checked lexer refused'
   for literal in s['literals']:
    t=literal['type']
    if literal.get('yul') or t=='address':
     spelling=literal['value'].replace('_','')
     compiler.append(fractions.Fraction(int(spelling,16 if spelling.startswith('0x') else 10)))
    elif re.fullmatch(r'int_const -?\d+',t):compiler.append(fractions.Fraction(int(t.split()[1])))
    else:
     m=re.fullmatch(r'rational_const (-?\d+) / (\d+)',t)
     assert m,('unhandled exact compiler numeric type',t)
     compiler.append(fractions.Fraction(int(m[1]),int(m[2])))
   assert values==compiler,('exact numeric value disagreement',l['id'],values,compiler)
  difference=l['lexOk']!=s['accepted']
  assert difference==(l['id'] in notes),('unrecorded or disappeared stage difference',l['id'])
  result.append(dict(id=l['id'],mode=l['mode'],spelling=l['spelling'],lexical_acceptance=l['lexOk'],compiler_acceptance=s['accepted'],raw_numeric=l['numeric'],raw_yul=l['yul'],lean_values=list(map(ratio,values)),compiler_values=list(map(ratio,compiler)),compiler_errors=s['errors'],stage_difference=notes.get(l['id'])))
 return dict(boundary='Finite paired observations, not universal compiler parity. Every case is retained; stage differences do not restrict any decoder theorem.',results=result)

if __name__=='__main__':
 packet=compute();path=folder/'differential.json'
 if '--record' in sys.argv:path.write_text(json.dumps(packet,indent=2)+'\n')
 else:assert json.loads(path.read_text())==packet,'paired differential record drifted'
 print(f"differential: {len(packet['results'])} paired spellings, {sum(r['compiler_acceptance'] for r in packet['results'])} exact accepted values, {sum(r['stage_difference'] is not None for r in packet['results'])} explicit stage differences")
