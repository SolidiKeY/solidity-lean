import Solidity.Lowering.V07.SignedComplement
import Solidity.Lowering.V07.SignedNegation

namespace Solidity.Lowering.V07.SignedComplementControls
open SignedComplement
open SignedWidthCasts (ty)
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)

def t := ty 8 (by decide)
def src := WordCastControls.source t 5 7 (by decide) (by decide)
def tgt := WordCastControls.target t 5 7 (by decide) (by decide)
def range_client := minus_one_range 8 (by decide)
def value_source_client (checked : Bool) := source_value checked 8 (by decide) (D := E.layout) 5 (by decide)
def value_target_client := value_run 8 (by decide) tgt (.simple (.local .here)) 5 (by decide) rfl

def operand_source_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_of_run 8 (by decide) (globals p) {F0 with checked := checked} (fuel+1)
    src src (.local .here) 5 (by decide) rfl

def local_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  local_transport 8 (by decide) (globals p) {F0 with checked := checked} fuel src tgt
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t 5 7 (by decide) (by decide)) true 5 (by decide) rfl

def repeated_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  local_transport 8 (by decide) (globals p) {F0 with checked := checked} fuel src tgt
    (fun _ : Bool => WordCastControls.si t true) (fun _ : Bool => WordCastControls.ti t true)
    ((WordCastControls.initial t 5 7 (by decide) (by decide)).reindex (fun _ : Bool => true))
    false 5 (by decide) rfl

def extension_client := DeferredSource.Operand.run_wk
  (DeferredSource.Operand.ofSrc (Src.val (complementValue 8 (.simple (.local .here)))))
  (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)

def live_caller : ∃ r : HRef tgt.H bytesR,
    TEnv.get (.there (.there .here)) tgt.env = some r ∧ tgt.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory

def check (p : Roadmap.Pipeline) (checked : Bool) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (n : Int) : Bool :=
  let x := (ty bits valid).wrap n
  let hx := (ty bits valid).wrap_mem n
  let y := (ty bits valid).wrap 7
  let hy := (ty bits valid).wrap_mem 7
  let source := WordCastControls.source (ty bits valid) x y hx hy
  let target := WordCastControls.target (ty bits valid) x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := checked} 2
    (.unary .bitNot (.local .here))).run source with
    | (.ok (.val v),out) => match v.key,(out.1.get .here).key,(out.1.get (.there .here)).key with
      | some v,some x,some y => some (v,x,y) | _,_,_ => none
    | _ => none
  let tr := match (complementValue bits (.simple (.local .here))).evalT target with
    | .ok v => some (v.val,(TEnv.get .here target.env).val,(TEnv.get (.there .here) target.env).val)
    | _ => none
  sr == some ((ty bits valid).wrap (-x-1),x,y) && tr == sr

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  (List.finRange 32).all fun i =>
  let bits := 8*(i.val+1)
  have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
  [(ty bits valid).lo,(ty bits valid).hi,-1,0,1,5].all (check p checked bits valid)))
/-- info: [some (-6), some (-5), some 6] -/
#guard_msgs in
#eval IO.println (reprStr [
  match (complementValue 8 (.simple (.local .here))).evalT tgt with | .ok v => some v.val | _ => none,
  match (SignedNegation.negValue 8 (.simple (.local .here))).evalT tgt with | .ok v => some v.val | _ => none,
  match (SignedNarrowSubtraction.subValue 8 (.simple (.local .here))
    (.simple (.lit (-1) (by decide)))).evalT tgt with | .ok v => some v.val | _ => none])
end Solidity.Lowering.V07.SignedComplementControls

/-- info: 'Solidity.Lowering.V07.SignedComplementControls.range_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplementControls.range_client

/-- info: 'Solidity.Lowering.V07.SignedComplementControls.value_source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplementControls.value_source_client

/-- info: 'Solidity.Lowering.V07.SignedComplementControls.value_target_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplementControls.value_target_client

/-- info: 'Solidity.Lowering.V07.SignedComplementControls.operand_source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplementControls.operand_source_client

/-- info: 'Solidity.Lowering.V07.SignedComplementControls.local_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplementControls.local_client

/-- info: 'Solidity.Lowering.V07.SignedComplementControls.repeated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplementControls.repeated_client

/-- info: 'Solidity.Lowering.V07.SignedComplementControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplementControls.extension_client

/-- info: 'Solidity.Lowering.V07.SignedComplementControls.live_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplementControls.live_caller
