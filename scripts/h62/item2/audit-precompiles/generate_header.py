#!/usr/bin/env python3
"""Guard regression: BLAKE size/flag/gas predicates must belong to one input; preserve short-header padding."""
import argparse,json,re
from census import census,ROOT
from inventory import split_declaration,groups

def generate():
 s="""import SolidityBridge.PrecompileAgreement.Controls
import Lean

/-! Guarded regressions: short nonzero headers must retain the padding factor;
the four-byte common domain and zero-header exception must stay distinct;
validation size/flag/affordability must hold jointly for the same input;
malformed-length membership must be witnessed, not assumed. Reuses the general
frozen padding and validation laws, without comparing compression output.
Private helper instances use their actual imported constants and ordinary
kernel term checking. No native crypto or compiler-success claim is made. -/
open Lean Elab Term in
elab "audit_header_private%" id:ident : term => do
  let env ← getEnv
  let suffix := "." ++ id.getId.toString
  let found := env.constants.toList.filter fun (n, _) =>
    n.toString.startsWith "_private.SolidityBridge.PrecompileAgreement." && n.toString.endsWith suffix
  unless found.length = 1 do throwError "expected one frozen private constant"
  let (name, info) := found.head!
  unless info.levelParams.isEmpty do throwError "unexpected universe parameters"
  return mkConst name

namespace H62.AuditPrecompiles.Successor.Header
open Solidity Solidity.Precompiles Solidity.Roadmap.Evm EvmYul
open SolidityBridge.PrecompileAgreement.Controls (input filled)

def shortHeader : ByteArray := ⟨#[1]⟩
def smallHeader : ByteArray := ⟨#[0,0,0,1,2]⟩
def zeroHeader : ByteArray := ⟨#[0]⟩
def validZero : ByteArray := ⟨Array.replicate 213 0⟩
def validOne : ByteArray := ⟨(Array.replicate 212 (0 : UInt8)).push 1⟩
def invalidFlag : ByteArray := ⟨(Array.replicate 212 (0 : UInt8)).push 2⟩

private theorem header_decode (d : ByteArray) :
    fromByteArrayBigEndian (d.extract 0 4) = ofBE ((d.toList.take 4).map UInt8.toNat) := by
  simp only [fromByteArrayBigEndian, SolidityBridge.PrecompileAgreement.big_reader,
    SolidityBridge.PrecompileAgreement.first_four]

"""
 hp={'blake_zero_header':1,'blake_price':1,'blake_gas':1,'blake_valid':3,'blake_insufficient':1,'blake_invalid_flag':2,'blake_valid_one':3,'blake_invalid_size':1,'blake_zero_gas':1,'blake_malformed_lengths':1};names=[]
 for f in census()['files']:
  for row in f['declarations']:
   name=row['name'].split('.')[-1]
   if f['path']!='Bridge/SolidityBridge/PrecompileAgreement/Header.lean' and name!='blake_malformed_lengths':continue
   bs,result=split_declaration(row);gs=groups(bs);hcount=hp.get(name,0);params=gs[:-hcount] if hcount else gs;proofs=gs[-hcount:] if hcount else [];wn=name+('_joint' if hcount else '_data');names.append(wn)
   di='validZero' if name=='blake_valid' else 'validOne' if name=='blake_valid_one' else 'invalidFlag' if name=='blake_invalid_flag' else 'zeroHeader' if name in ['blake_zero_header','blake_zero_gas'] else 'smallHeader'
   vals={'bs':'[1,2]','b':'3','n':'1','d':'shortHeader' if name=='blake_padding' else di,'σ':'default','g':'(UInt256.ofNat 0)' if name=='blake_insufficient' else '(UInt256.ofNat 50001)','A':'default','I':'(input '+di+')'};vs=[vals[n] for g in params for n in g['names']]
   target=' ∧ '.join([g['type'] for g in proofs]+['('+result+')'])
   s+='-- Frozen source: '+row['name']+'\ntheorem '+wn+' : ∃ '+' '.join(g['source'] for g in params)+', '+target+' := by\n'
   hnames=[]
   for g in proofs:
    hn=g['names'][0];typ=g['type']
    for n in sorted([n for x in params for n in x['names']],key=len,reverse=True):typ=re.sub(r"(?<![\w'])"+re.escape(n)+r"(?![\w'])",lambda _:vals[n],typ)
    if 'fromByteArrayBigEndian' in typ:
     rewrites=['header_decode','SolidityBridge.PrecompileAgreement.byte_list']
     if hn in ['enough','short']:rewrites+=['SolidityBridge.PrecompileAgreement.ofNat_nat '+('0' if hn=='short' else '50001')+' (by decide)']
     proof='rw ['+', '.join(rewrites)+']; decide +kernel'
    else:proof='decide +kernel'
    s+='  have '+hn+' : '+typ+' := by '+proof+'\n';hnames.append(hn)
   fn='(audit_header_private% '+row['name']+')' if row['visibility']=='private' else row['name'];s+='  exact ⟨'+', '.join(vs+hnames+[fn+' '+' '.join(vs+hnames)])+'⟩\n\n'
 assert len(names)==17
 pinfile=ROOT/'tests/h62/item2/audit-precompiles/header-pins.json'
 if pinfile.exists():
  pins=json.loads(pinfile.read_text());assert len(pins)==17
  messages=json.loads((ROOT/'tests/h62/item2/audit-precompiles/header-pin-messages.json').read_text())
  for n in names:
   full='H62.AuditPrecompiles.Successor.Header.'+n;msg=messages[full];match=re.fullmatch("'"+re.escape(full)+"' (?:depends on axioms: \\[([^\\]]*)\\]|does not depend on any axioms)",msg,re.S);assert match
   axes=sorted(a.strip() for a in match[1].split(',') if a.strip()) if match[1] else [];assert axes==pins[full] and set(axes)<=set(['propext','Classical.choice','Quot.sound'])
   s+='/-- info: '+msg+' -/\n#guard_msgs in\n#print axioms '+n+'\n'
 else:s+='\n'.join('#print axioms '+n for n in names)+'\n'
 s+='run_cmd Lean.logInfo "HEADER_APPLICABILITY_PASS joint=10 data=7"\nend H62.AuditPrecompiles.Successor.Header\n';return s
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();s=generate();dst=ROOT/'tests/h62/item2/audit-precompiles/BridgeHeaderWitnesses.lean'
 if a.check:assert dst.read_text()==s
 else:dst.write_text(s)
 print('HEADER_GENERATED17 original cases;10joint/7data')
