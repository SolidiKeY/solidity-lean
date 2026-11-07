#!/usr/bin/env python3
"""Generate exact frozen IDENTITY applicability types; never replace interfaces."""
from pathlib import Path
import json
from census import census,ROOT
from inventory import split_declaration,groups
rows=[d for f in census()['files'] if f['path']=='Bridge/SolidityBridge/PrecompileAgreement/Identity.lean' for d in f['declarations']]
assert len(rows)==10
s="""import SolidityBridge.PrecompileAgreement.Identity

/-! Exact frozen IDENTITY applicability and full-type audit at v4.24.
All data and proof hypotheses belong to the same input. The large-array
case is symbolic, not an executable allocation or a v4.35 migration claim. -/
namespace H62.AuditPrecompiles.Successor
open Solidity.Precompiles EvmYul

def sample : ByteArray := ⟨#[0, 128, 255, 1]⟩
def input (d : ByteArray) : ExecutionEnv .EVM :=
  {(default : ExecutionEnv .EVM) with calldata := d}

private theorem sample_cost : identityGas (input sample).calldata.toList = 18 := by
  rw [SolidityBridge.PrecompileAgreement.identity_gas]
  change 15 + 3 * ((4 + 31) / 32) = 18
  decide

"""
proofs={'identity_success':('enough','identityGas (input sample).calldata.toList ≤ (UInt256.ofNat 18).toNat'),
'identity_failure':('short','(UInt256.ofNat 17).toNat < identityGas (input sample).calldata.toList'),
'identity_charged':('enough','identityGas (input sample).calldata.toList ≤ (UInt256.ofNat 18).toNat'),
'identity_exact':('fits','identityGas (input sample).calldata.toList < UInt256.size'),
'identity_one_short':('fits','identityGas (input sample).calldata.toList < UInt256.size'),
'identity_unaffordable':('huge','UInt256.size ≤ identityGas (input d).calldata.toList')}
names=[]
for row in rows:
 name=row['name'].split('.')[-1];binders,result=split_declaration(row);gs=groups(binders);kind='joint' if name in proofs else 'data';wn=name+'_'+kind;names.append(wn)
 params=gs[:-1] if kind=='joint' else gs
 vals={'d':'sample','σ':'default','g':'(UInt256.ofNat 17)' if name=='identity_failure' else '(UInt256.ofNat 18)','A':'default','I':'(input d)' if name=='identity_unaffordable' else '(input sample)'}
 values=[vals[n] for g in params for n in g['names']]
 exists=' '.join(g['source'] for g in params)
 target=(gs[-1]['type']+' ∧ ('+result+')') if kind=='joint' else result
 s+='theorem '+wn+' : ∃ '+exists+', '+target+' := by\n'
 if kind=='joint':
  hn,ht=proofs[name]
  if name=='identity_unaffordable':
   s+='  let d : ByteArray := ⟨Array.replicate (32 * UInt256.size) 0⟩\n'
   s+='  have cost : identityGas (input d).calldata.toList = 15 + 3 * UInt256.size := by\n    rw [SolidityBridge.PrecompileAgreement.identity_gas]\n    simp only [input, d, ByteArray.size, Array.size_replicate]\n    omega\n'
   s+='  have huge : '+ht+' := by rw [cost]; omega\n'
  else:
   proof_step="rw [sample_cost]" if hn=='fits' else ("rw [sample_cost, SolidityBridge.PrecompileAgreement.ofNat_nat 17 (by decide)]" if hn=='short' else "rw [sample_cost, SolidityBridge.PrecompileAgreement.ofNat_nat 18 (by decide)]")
   s+='  have '+hn+' : '+ht+' := by '+proof_step+('' if hn=='enough' else '; decide')+'\n'
  proof=row['name']+' '+' '.join(values)+' '+hn;s+='  exact ⟨'+', '.join(values+[hn,proof])+'⟩\n\n'
 else:s+='  exact ⟨'+', '.join(values+[row['name']+' '+' '.join(values)])+'⟩\n\n'
 s+='-- Exact frozen full type: '+row['name']+'\n'
 s+='set_option linter.unusedVariables false in\nexample : ∀ '+binders+', '+result+' := @'+row['name']+'\n\n'
s+="""def rejectAll (_ : AccountMap .EVM) (_ : UInt256) (_ : Substate)
    (_ : ExecutionEnv .EVM) : Bool := false

theorem rejectAll_refused : rejectAll default (UInt256.ofNat 18) default (input sample) ≠
    (Ξ_ID default (UInt256.ofNat 18) default (input sample)).1 := by
  have enough : identityGas (input sample).calldata.toList ≤ (UInt256.ofNat 18).toNat := by
    rw [sample_cost, SolidityBridge.PrecompileAgreement.ofNat_nat 18 (by decide)]
  rw [SolidityBridge.PrecompileAgreement.identity_success _ _ _ _ enough]
  decide

theorem identity_sample_boundary :
    (Ξ_ID default (UInt256.ofNat 17) default (input sample)).1 = false ∧
    (Ξ_ID default (UInt256.ofNat 18) default (input sample)).1 = true := by
  have enough : identityGas (input sample).calldata.toList ≤ (UInt256.ofNat 18).toNat := by
    rw [sample_cost, SolidityBridge.PrecompileAgreement.ofNat_nat 18 (by decide)]
  have short : (UInt256.ofNat 17).toNat < identityGas (input sample).calldata.toList := by
    rw [sample_cost, SolidityBridge.PrecompileAgreement.ofNat_nat 17 (by decide)]
    decide
  constructor
  · rw [SolidityBridge.PrecompileAgreement.identity_failure _ _ _ _ short]
  · rw [SolidityBridge.PrecompileAgreement.identity_success _ _ _ _ enough]

theorem sample_nonempty : sample.size = 4 := rfl

"""
names+=['rejectAll_refused','identity_sample_boundary','sample_nonempty']
pins=json.loads((ROOT/'tests/h62/item2/audit-precompiles/successor-identity-pins.json').read_text())
for n in names:
 full='H62.AuditPrecompiles.Successor.'+n;axes=pins[full]
 ordered=[a for a in ['propext','Classical.choice','Quot.sound'] if a in axes]
 # Actual pretty-printer emits propext, then choice, then Quot.sound here.
 message="'"+full+"' "+(('depends on axioms: ['+', '.join(ordered)+']') if axes else 'does not depend on any axioms')
 s+='/-- info: '+message+' -/\n#guard_msgs in\n#print axioms '+n+'\n'
s+='run_cmd Lean.logInfo \"IDENTITY_APPLICABILITY_PASS joint=6 data=4 guards=13 controls=3\"\nend H62.AuditPrecompiles.Successor\n'

import argparse
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
dst=ROOT/'tests/h62/item2/audit-precompiles/BridgeIdentityWitnesses.lean'
if a.check:assert dst.read_text()==s,'frozen identity audit generation differs'
else:dst.write_text(s)
print('Generated10 cases:6 joint proof-premise witnesses,4 data-domain samples,10 exact whole-type assignments')
