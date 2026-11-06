#!/usr/bin/env python3
"""Frozen BLS applicability; retain simultaneous nonzero table constraints."""
import argparse,json
from census import census,ROOT
from inventory import split_declaration,groups

def generate():
 s="""import Lean.Elab.Command
import Solidity.Precompiles.Bls12381

/-! Guards against counting separate MSM table premises as a simultaneous
witness, silently choosing an empty input domain, or treating failure laws as
native cryptographic equality. Constant table lookup is general in length,
index and value; all original BLS cases retain unchanged conclusions. -/
namespace H62.AuditPrecompiles.Successor.Bls
open Solidity.Precompiles Solidity.Roadmap.Evm
open Solidity.Precompiles.Bls12381

theorem replicate_getD (n i v : Nat) : (List.replicate n v).getD i v = v := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem constant_table_bounds (v i : Nat) :
    (i+1)*(List.replicate 128 v).getD i v ≤
      (i+2)*(List.replicate 128 v).getD (i+1) v := by
  rw [replicate_getD, replicate_getD]
  exact Nat.mul_le_mul_right v (Nat.le_succ (i+1))

"""
 names=['replicate_getD','constant_table_bounds'];count=0
 for f in census()['files']:
  if f['path']!='Solidity/Precompiles/Bls12381.lean':continue
  for row in f['declarations']:
   n=row['name'].split('.')[-1];bs,result=split_declaration(row);gs=groups(bs);count+=1
   if n in ['msmGas_succ','msmGas_mono']:
    mono=n=='msmGas_mono';wn=n+'_joint';names.append(wn)
    s+='theorem '+wn+' : ∃ (c : Nat) (table : List Nat) (cap k l : Nat),\n    table.length = 128 ∧\n    (∀ i < 128, (i+1)*table.getD i cap ≤ (i+2)*table.getD (i+1) cap) ∧\n    k ≤ l ∧ msmGas c table cap k ≤ msmGas c table cap '+('l' if mono else '(k+1)')+' := by\n'
    s+='  have hl : (List.replicate 128 1000).length = 128 := List.length_replicate\n  have ht : ∀ i < 128, (i+1)*(List.replicate 128 1000).getD i 1000 ≤ (i+2)*(List.replicate 128 1000).getD (i+1) 1000 := fun i _ => constant_table_bounds 1000 i\n'
    s+='  exact ⟨1, List.replicate 128 1000, 1000, 1, 2, hl, ht, by decide, '+n+' 1 _ 1000 '+('hl ht (by decide)' if mono else '1 hl ht')+'⟩\n\n';continue
   if n in ['g1MsmGas_mono','g2MsmGas_mono','pairingGas_mono']:
    wn=n+'_joint';names.append(wn)
    s+='theorem '+wn+' : ∃ d e : Bytes, d.length ≤ e.length ∧ ('+result+') := by\n  have h : ([1] : Bytes).length ≤ ([1,2] : Bytes).length := by decide\n  exact ⟨[1], [1,2], h, '+n+' h⟩\n\n';continue
   if n=='bind_some_eq_none':
    wn=n+'_data';names.append(wn)
    s+='theorem '+wn+' : ∃ (α β : Type) (o : Option α) (f : α → β), '+result+' :=\n  ⟨Unit, Unit, some (), id, '+n+' (some ()) id⟩\n\n';continue
   wn=n+('_data' if gs else '_fidelity');names.append(wn)
   s+='-- Frozen source: '+row['name']+'\ntheorem '+wn+' : '+('∃ '+' '.join(g['source'] for g in gs)+', ' if gs else '')+result+' :=\n  '
   vals=['[1]' for g in gs for _ in g['names']]
   s+=('⟨'+', '.join(vals)+', '+n+' '+' '.join(vals)+'⟩' if gs else n)+'\n\n'
 assert count==18
 pins=ROOT/'tests/h62/item2/audit-precompiles/bls-pin-messages.json'
 messages=json.loads(pins.read_text()) if pins.exists() else {}
 for n in names:
  full='H62.AuditPrecompiles.Successor.Bls.'+n
  if full in messages:s+='/-- info: '+messages[full]+' -/\n#guard_msgs in\n'
  s+='#print axioms '+n+'\n'
 s+='run_cmd Lean.logInfo "CORE_APPLICABILITY_PASS module=Bls original=18 guards=20"\nend H62.AuditPrecompiles.Successor.Bls\n'
 return s
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();s=generate();dst=ROOT/'tests/h62/item2/audit-precompiles/BlsWitnesses.lean'
 if a.check:assert dst.read_text()==s
 else:dst.write_text(s)
 print('BLS_GENERATED original=18 auxiliary=2')
