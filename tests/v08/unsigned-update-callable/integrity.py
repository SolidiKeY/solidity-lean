#!/usr/bin/env python3
"""Portable source/guard corruption checks; never a kernel or EVM verdict."""
import pathlib,json,hashlib,re
root=pathlib.Path(__file__).resolve().parents[3]
d=pathlib.Path(__file__).resolve().parent
pins=json.loads((d/'axiom-sets.json').read_text());bindings=json.loads((d/'source-bindings.json').read_text())
def check(sources,sets):
 assert len(sets)==31
 joined='\n'.join(sources.values())
 observed={}
 for name,report in re.findall(r"/-- info: '([^']+)' (.*?) -/\s*#guard_msgs \(whitespace := lax\) in\s*#print axioms [^\n]+",joined,re.S):
  ax=re.search(r'\[([^\]]*)\]',report)
  observed[name]=[] if ax is None else [v.strip() for v in ax.group(1).split(',')]
 assert observed==sets
 declared={n for n in re.findall(r'^#print axioms ([^\n]+)',joined,re.M)}
 assert declared==set(sets)
 for name,axes in sets.items():
  assert set(axes)<=set(['propext','Classical.choice','Quot.sound'])
  joined='\n'.join(sources.values())
  assert '#print axioms '+name+'\n' in joined
 for name,text in sources.items():
  assert hashlib.sha256(text.encode()).hexdigest()==bindings[name]
  assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',text)
  assert '#guard_msgs (whitespace := lax) in' in text
sources={p:(root/p).read_text() for p in bindings};check(sources,pins)
count=0
for needle in ['#guard_msgs (whitespace := lax) in','source_expression','extra+17','IntValueRel','wrong_postfix_return','wrong_caller_snapshot']:
 bad=dict(sources)
 for p,t in bad.items():
  if needle in t:bad[p]=t.replace(needle,needle+'_corrupt',1);break
 try:check(bad,pins)
 except AssertionError:count+=1
 else:raise AssertionError('accepted corruption '+needle)
bad=dict(pins);bad[next(iter(bad))]=['sorryAx']
try:check(sources,bad)
except AssertionError:count+=1
else:raise AssertionError('accepted nonstandard axiom')
print('PASS portable binding/guard positive; '+str(count)+' in-memory corruption controls; not kernel validation')

bad={n:list(a) for n,a in pins.items()};name=next(n for n,a in bad.items() if a);bad[name]=[]
try:check(sources,bad)
except AssertionError:print('PASS exact standard-subset pin corruption rejected (8 total corruption cases)')
else:raise AssertionError('accepted changed standard axiom set')
