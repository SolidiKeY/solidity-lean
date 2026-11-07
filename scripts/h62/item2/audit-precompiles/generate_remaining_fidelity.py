#!/usr/bin/env python3
"""Retain all remaining frozen core types, including dependent typing proofs."""
import argparse
from census import census,ROOT
from inventory import split_declaration

def generate():
 out=['import Solidity.Precompiles.Osaka','import Solidity.Stipend.Rule','',
 '/-! Guards against source census fidelity dropping an implicit Contract or',
 'dependent power typing proof. All41 remaining frozen core types are assigned',
 'directly from imported constants; this is not a simultaneous witness or',
 'an actual compiler-success theorem. -/',
 'open Solidity Solidity.Precompiles Solidity.Roadmap.Evm','open Solidity.Precompiles.Bls12381 (r)','']
 total=0
 for f in census()['files']:
  if f['path'] not in ['Solidity/Precompiles/Bls12381.lean','Solidity/Precompiles/PointEval.lean','Solidity/Precompiles/Osaka.lean','Solidity/Stipend/Rule.lean']:continue
  for row in f['declarations']:
   bs,goal=split_declaration(row)
   if f['path']=='Solidity/Stipend/Rule.lean':bs='{C : Contract} '+bs
   full=('∀ '+bs+', '+goal) if bs else goal
   ns=row['name'].rsplit('.',1)[0]
   out+=['namespace '+ns,'-- Frozen source: '+row['name'],'set_option linter.unusedVariables false in','example : '+full+' := @'+row['name'],'end '+ns,''];total+=1
 assert total==41
 out+=['run_cmd Lean.logInfo "REMAINING_CORE_FULL_TYPE_FIDELITY_PASS total=41"']
 return '\n'.join(out)+'\n'
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();s=generate();dst=ROOT/'tests/h62/item2/audit-precompiles/RemainingCoreFidelity.lean'
 if a.check:assert dst.read_text()==s
 else:dst.write_text(s)
 print('REMAINING_CORE_FROZEN_TYPES41')
