#!/usr/bin/env python3
"""Generate direct full-type checks from the frozen source census, no weakening."""
from pathlib import Path
from census import census, ROOT
MODULES=['Field','Basic','Modexp','Bn254','Blake2f','P256']
def generate():
 out=['import Solidity.Precompiles.'+m for m in MODULES]
 out += ['', '/-! Every example assigns the original constant directly at its entire frozen',
         'source type, including all data and proof binders. This does not replace',
         'a simultaneous applicability witness or owner compiler-success theorem.', 'Unused binder lint is local to these type checks: every frozen proof binder', 'is retained with its original name even when absent from the conclusion. -/',
         'open Solidity.Roadmap.Evm (Bytes)', '']
 count=0
 for f in census()['files']:
  if f['path'] not in ['Solidity/Precompiles/'+m+'.lean' for m in MODULES]: continue
  for d in f['declarations']:
   assert d['visibility']=='public'
   short=d['name'].rsplit('.',1)[-1]
   prefix='theorem '+short
   assert d['signature'].startswith(prefix)
   rest=d['signature'][len(prefix):].strip()
   depth=0; split=None
   for i,c in enumerate(rest):
    if c in '([{': depth+=1
    elif c in ')]}': depth-=1
    elif c==':' and depth==0: split=i;break
   assert split is not None
   binders=rest[:split].strip();goal=rest[split+1:].strip()
   full=('∀ '+binders+', '+goal) if binders else goal
   namespace=d['name'].rsplit('.',1)[0]
   out += ['namespace '+namespace, '-- Frozen source: '+d['name'],
           'set_option linter.unusedVariables false in', 'example : '+full+' := @'+d['name'], 'end '+namespace, '']
   count+=1
 assert count==24
 return '\n'.join(out).rstrip()+'\n'
if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 dest=ROOT/'tests/h62/item2/audit-precompiles/TypeFidelity.lean'
 text=generate()
 if a.check:
  assert dest.read_text()==text,'frozen type-check generation differs'
 else: dest.write_text(text)
 print('FROZEN_TYPE_CHECKS 24 direct full-type assignments (applicability separate)')
