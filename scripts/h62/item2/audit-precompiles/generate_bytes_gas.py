#!/usr/bin/env python3
"""Exact frozen Bytes/Gas applicability; no omitted bound or success-flag premise."""
import argparse,json
from census import census,ROOT
from inventory import split_declaration,groups

def generate():
 s="""import SolidityBridge.PrecompileAgreement.Gas

/-! Guarded regressions: gas subtraction must retain affordability; conversion
must retain the UInt256 size bound; word rounding must distinguish the multiple,
first, last and next-word positions; malformed/error-capable vendor gas rows
must retain their actual success flag. The private list_loop case must not be
omitted from the exactly-once census. word_rounding_boundaries is general in n.
These are frozen-model applicability samples, not native crypto equality or
compiler-success claims. -/
namespace H62.AuditPrecompiles.Successor.BytesGas
open Solidity.Precompiles Solidity.Roadmap.Evm EvmYul

def sample : ByteArray := ⟨#[0, 128, 255, 1]⟩
def input : ExecutionEnv .EVM :=
  {(default : ExecutionEnv .EVM) with calldata := sample}

theorem word_rounding_boundaries (n : Nat) :
    words (32*n) = n ∧ words (32*n+1) = n+1 ∧ words (32*n+31) = n+1 ∧
    words (32*n+32) = n+1 ∧
    words n = n/32 + if n%32=0 then 0 else 1 := by
  exact ⟨SolidityBridge.PrecompileAgreement.words_multiple n,
    SolidityBridge.PrecompileAgreement.words_next n,
    SolidityBridge.PrecompileAgreement.words_last n,
    SolidityBridge.PrecompileAgreement.words_boundary n,
    SolidityBridge.PrecompileAgreement.words_rounding n⟩

"""
 names=['word_rounding_boundaries'];count=0
 for f in census()['files']:
  if f['path'] not in ['Bridge/SolidityBridge/PrecompileAgreement/Bytes.lean','Bridge/SolidityBridge/PrecompileAgreement/Gas.lean']:continue
  for row in f['declarations']:
   name=row['name'].split('.')[-1]
   if name=='address_table':continue
   bs,result=split_declaration(row);gs=groups(bs);joint=name in ['ofNat_nat','subtract_nat'];params=gs[:-1] if joint else gs;wn=name+('_joint' if joint else '_data');names.append(wn);count+=1
   vals={'b':'sample','d':'sample','i':'0','r':'([] : List UInt8)','n':'15' if name=='subtract_nat' else '18' if name=='ofNat_nat' else '1','p':'Precompile.identity','σ':'default','g':'(UInt256.ofNat 50001)' if not joint else '(UInt256.ofNat 18)','A':'default','I':'input'}
   vs=[vals[n] for g in params for n in g['names']];target=gs[-1]['type']+' ∧ ('+result+')' if joint else result
   s+='-- Frozen source: '+row['name']+'\ntheorem '+wn+' : ∃ '+' '.join(g['source'] for g in params)+', '+target+' := by\n'
   if name=='list_loop':
    s+='  refine ⟨sample, 0, [], ?_⟩\n  change sample.toList = sample.data.toList\n  exact SolidityBridge.PrecompileAgreement.byte_list sample\n\n';continue
   if name=='ofNat_nat':s+='  have h : 18 < UInt256.size := by decide\n'
   if name=='subtract_nat':s+='  have h : 15 ≤ (UInt256.ofNat 18).toNat := by\n    rw [SolidityBridge.PrecompileAgreement.ofNat_nat 18 (by decide)]\n    decide\n'
   app=row['name']+' '+' '.join(vs)+(' h' if joint else '')
   s+='  exact ⟨'+', '.join(vs+(['h'] if joint else [])+[app])+'⟩\n\n'
 assert count==21
 pinfile=ROOT/'tests/h62/item2/audit-precompiles/bytes-gas-pins.json'
 if pinfile.exists():
  pins=json.loads(pinfile.read_text());assert len(pins)==len(names)==22
  for n in names:
   full='H62.AuditPrecompiles.Successor.BytesGas.'+n;axes=pins[full];ordered=[a for a in ['propext','Classical.choice','Quot.sound'] if a in axes]
   message="'"+full+"' "+(('depends on axioms: ['+', '.join(ordered)+']') if axes else 'does not depend on any axioms')
   s+='/-- info: '+message+' -/\n#guard_msgs in\n#print axioms '+n+'\n'
 else:s+='\n'.join('#print axioms '+n for n in names)+'\n'
 s+='run_cmd Lean.logInfo "BYTES_GAS_APPLICABILITY_PASS joint=2 data=19 guards=22"\nend H62.AuditPrecompiles.Successor.BytesGas\n'
 return s
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();s=generate();dst=ROOT/'tests/h62/item2/audit-precompiles/BridgeBytesGasWitnesses.lean'
 if a.check:assert dst.read_text()==s
 else:dst.write_text(s)
 print('BYTES_GAS_GENERATED 21original cases + general rounding lemma')
