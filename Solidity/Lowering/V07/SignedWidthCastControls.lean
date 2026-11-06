import Solidity.Lowering.V07.SignedWidthCasts
import Solidity.Lowering.V07.WordCastControls

namespace Solidity.Lowering.V07.SignedWidthCastControls
open SignedWidthCasts Source.SemanticsExamples
open WordCastControls (source target si ti initial)
open MixedAssignmentControls (C E globals storageRef)

def src := source (ty 16 (by decide)) 128 7 (by decide) (by decide)
def tgt := target (ty 16 (by decide)) 128 7 (by decide) (by decide)
def embedding := word_range 16 (by decide) 128 (by decide)
def wrapping := wrap_eq 8 (by decide) 128
def admissible := allowed 16 (by decide) E 8 (by decide)
def value := value_run 16 (by decide) tgt 8 (by decide) (.simple (.local .here)) 128 (by decide) rfl
def source_value (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_of_run 16 (by decide) (globals p) F0 (fuel+1) src src (.local .here) 8 (by decide) 128 (by decide) rfl
def source_local (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_local_run 16 (by decide) (globals p) F0 fuel src .here 8 (by decide) 128 (by decide) rfl
def target_assignment := assigned_run 16 (by decide) tgt 8 (by decide) (.there .here) .here 128 (by decide) rfl
def assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 16 (by decide) 8 (by decide) (globals p) F0 fuel src tgt (si (ty 16 (by decide))) (ti (ty 16 (by decide)))
    (initial (ty 16 (by decide)) 128 7 (by decide) (by decide)) false true 128 (by decide) rfl
def extension := assignment_extension 16 (by decide) 8 (by decide) tgt (.there .here) .here 128 (by decide) rfl
  (Thin.drop (t := .val .bool) .refl) (true,tgt.env)

-- Repeated aliases and equal contents at different identities remain distinct cases.
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 16 (by decide) 8 (by decide) (globals p) F0 fuel src tgt
    (fun _ : Bool => si (ty 16 (by decide)) true) (fun _ : Bool => ti (ty 16 (by decide)) true)
    ((initial (ty 16 (by decide)) 128 7 (by decide) (by decide)).reindex (fun _ : Bool => true))
    false true 128 (by decide) rfl
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 16 (by decide) 8 (by decide) (globals p) F0 fuel
    (source (ty 16 (by decide)) 128 128 (by decide) (by decide)) (target (ty 16 (by decide)) 128 128 (by decide) (by decide))
    (si (ty 16 (by decide))) (ti (ty 16 (by decide))) (initial (ty 16 (by decide)) 128 128 (by decide) (by decide)) false true 128 (by decide) rfl

def check (p : Roadmap.Pipeline) (checked : Bool)
    (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (input : Int) : Bool :=
  let x := (ty fromBits fromValid).wrap input
  let hx := (ty fromBits fromValid).wrap_mem input
  let s := source (ty fromBits fromValid) x 0 hx
    ((ty fromBits fromValid).wrap_mem 0)
  let t := target (ty fromBits fromValid) x 0 hx
    ((ty fromBits fromValid).wrap_mem 0)
  let sr := match (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .int (ty bits valid)) (.local .here)
      (allowed fromBits fromValid E bits valid))).run s with
    | (.ok (.val v),_) => v.key | _ => none
  let tr := match (castValue bits (.simple (.local .here))).evalT t with
    | .ok v => some v.val | _ => none
  let q := x % ((2^bits : Nat) : Int)
  let expected := if q < ((2^(bits-1) : Nat) : Int) then q else q-((2^bits : Nat) : Int)
  sr == some expected && tr == sr

-- Source-wrapped boundaries, NOT admission of out-of-range constants.
--32sourcewidths×32destinations×2pipelines×2checkedflags×11inputs=45,056cases.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun c =>
  (List.finRange 32).all fun j => (List.finRange 32).all fun i =>
    let fromBits := 8*(j.val+1)
    let bits := 8*(i.val+1)
    have fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256 := by omega
    have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
    [0,127,128,255,256,257,-1,-128,-129,(ty fromBits fromValid).lo,(ty fromBits fromValid).hi].all
      fun input => check p c fromBits fromValid bits valid input))

def expr : Source.RExpr E [.int (ty 16 (by decide)),.int (ty 16 (by decide)),.bytes .memory,.bytes .storage]
    (.int (ty 8 (by decide))) :=
  .convExplicit (.assign (.local (.there .here)) (.local .here)) (allowed 16 (by decide) E 8 (by decide))
def sourcePair (p : Roadmap.Pipeline) : Option (Int × Int × Int) :=
  match (Source.evalPair (globals p) F0 8 expr (.local (.there .here))).run src with
  | (.ok (.val x,.val y),out) => match x.key,y.key,(out.1.get (.there .here)).key with
    | some x,some y,some z => some (x,y,z) | _,_,_ => none
  | _ => none

def targetPair (p : Roadmap.Pipeline) : Option (Int × Int × Int) :=
  match (assignReadPrefix p (.there .here) .here).run tgt with
  | .ok o =>
    let left : Val C [.val .int,.val .int,.val .int,.val .int,.mem bytesR,.alias bytesR] .int :=
      match p with | .legacy => .simple (.local .here) | .viaIR => .simple (.local (.there .here))
    let right : Idx [.val .int,.val .int,.val .int,.val .int,.mem bytesR,.alias bytesR] (.val .int) :=
      match p with | .legacy => .there .here | .viaIR => .here
    match (castValue 8 left).evalT o.st with
    | .ok x => some (x.val,(TEnv.get right o.st.env).val,(TEnv.get (.there (.there (.there .here))) o.st.env).val)
    | _ => none
  | _ => none
/-- info: [some (-128, 7, 128), some (-128, 128, 128), some (-128, 7, 128), some (-128, 128, 128)] -/
#guard_msgs in
#eval IO.println (reprStr [sourcePair .legacy,sourcePair .viaIR,targetPair .legacy,targetPair .viaIR])

-- Wrong stale capture7, omitted sign extension128 and narrowed caller−128 are rejected.
example : sourcePair .legacy ≠ some (7,7,128) := by decide
example : sourcePair .viaIR ≠ some (128,128,128) := by decide
example : targetPair .legacy ≠ some (-128,7,-128) := by decide
example : targetPair .viaIR ≠ targetPair .legacy := by decide

-- Execute the wrong stale local and omitted conversion, rather than only naming them.
/-- info: [some 7, some 128, some (-128)] -/
#guard_msgs in
#eval IO.println (reprStr [
  match (castValue 8 (.simple (.local (.there .here)))).evalT tgt with
    | .ok v => some v.val | _ => none,
  match (assignLocalOperand (.there .here) .here).run tgt with
    | .ok (_, .prim v) => some v.val | _ => none,
  match (assignedOperand 8 (.there .here) .here).run tgt with
    | .ok (_, .prim v) => some v.val | _ => none])

-- Actual wrong zero-extension agrees on low bits but loses the destination sign.
def negTarget := target (ty 16 (by decide)) (-1) 7 (by decide) (by decide)
/-- info: [some 255, some (-1)] -/
#guard_msgs in
#eval IO.println (reprStr [
  match (Val.unop .toInt rfl rfl (UnsignedCasts.castValue 8
    (.unop .toUint rfl rfl (.simple (.local .here))))).evalT negTarget with
    | .ok v => some v.val | _ => none,
  match (castValue 8 (.simple (.local .here))).evalT negTarget with
    | .ok v => some v.val | _ => none])

def out := tgt.setLocal (.there .here) (integerValue (ty 16 (by decide)) 128 (by decide))
example : out.heap = tgt.heap ∧ out.glob = tgt.glob ∧
    TEnv.get (.there (.there .here)) out.env = TEnv.get (.there (.there .here)) tgt.env ∧
    TEnv.get (.there (.there (.there .here))) out.env = some storageRef := ⟨rfl,rfl,rfl,rfl⟩
example : ∃ r : HRef tgt.H bytesR,
    TEnv.get (.there (.there .here)) tgt.env = some r ∧ tgt.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory

end Solidity.Lowering.V07.SignedWidthCastControls
