import Solidity.Lowering.V07.UnsignedCasts
import Solidity.Lowering.V07.WordCastControls

namespace Solidity.Lowering.V07.UnsignedCastControls
open UnsignedCasts Source.SemanticsExamples
open WordCastControls (source target si ti initial umax)
open MixedAssignmentControls (C E globals storageRef)

def src := source .u256 257 7 (by decide) (by decide)
def tgt := target .u256 257 7 (by decide) (by decide)
def admissible := allowed E 8 (by decide)
def value := value_run tgt 8 (by decide) (.simple (.local .here)) 257 (by decide) rfl
def source_value (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_of_run (globals p) F0 (fuel+1) src src (.local .here) 8 (by decide) 257 (by decide) rfl
def source_local (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_local_run (globals p) F0 fuel src .here 8 (by decide) 257 (by decide) rfl
def target_assignment := assigned_run tgt 8 (by decide) (.there .here) .here 257 (by decide) rfl
def assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel src tgt (si .u256) (ti .u256)
    (initial .u256 257 7 (by decide) (by decide)) false true 257 (by decide) rfl
def extension := assignment_extension 8 (by decide) tgt (.there .here) .here 257 (by decide) rfl
  (Thin.drop (t := .val .bool) .refl) (true,tgt.env)

-- Repeated aliases and equal contents at different identities remain distinct cases.
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel src tgt
    (fun _ : Bool => si .u256 true) (fun _ : Bool => ti .u256 true)
    ((initial .u256 257 7 (by decide) (by decide)).reindex (fun _ : Bool => true))
    false true 257 (by decide) rfl
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel
    (source .u256 257 257 (by decide) (by decide)) (target .u256 257 257 (by decide) (by decide))
    (si .u256) (ti .u256) (initial .u256 257 257 (by decide) (by decide)) false true 257 (by decide) rfl

def check (p : Roadmap.Pipeline) (checked : Bool) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi) : Bool :=
  let s := source .u256 x 7 hx (by decide)
  let t := target .u256 x 7 hx (by decide)
  let sr := match (Source.evalE (globals p) {F0 with checked := checked} 3
    (.convExplicit (τ := .int (UnsignedNarrowing.ty bits valid)) (.local .here) (allowed E bits valid))).run s with
    | (.ok (.val v),_) => v.key | _ => none
  let tr := match (castValue bits (.simple (.local .here))).evalT t with
    | .ok v => some v.val | _ => none
  sr == some (x % ((2^bits : Nat) : Int)) && tr == sr

-- All32 widths, both pipelines, both checked flags and five input boundaries.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun c =>
  (List.finRange 32).all fun i =>
    let bits := 8*(i.val+1)
    have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
    check p c bits valid 0 (by decide) && check p c bits valid 255 (by decide) &&
    check p c bits valid 256 (by decide) && check p c bits valid 257 (by decide) &&
    check p c bits valid umax (by decide)))

def expr : Source.RExpr E [.int .u256,.int .u256,.bytes .memory,.bytes .storage]
    (.int (UnsignedNarrowing.ty 8 (by decide))) :=
  .convExplicit (.assign (.local (.there .here)) (.local .here)) (allowed E 8 (by decide))
def sourcePair (p : Roadmap.Pipeline) : Option (Int × Int × Int) :=
  match (Source.evalPair (globals p) F0 8 expr (.local (.there .here))).run src with
  | (.ok (.val x,.val y),out) => match x.key,y.key,(out.1.get (.there .here)).key with
    | some x,some y,some z => some (x,y,z) | _,_,_ => none
  | _ => none

def targetPair (p : Roadmap.Pipeline) : Option (Int × Int × Int) :=
  match (assignReadPrefix p (.there .here) .here).run tgt with
  | .ok o =>
    let left : Val C [.val .uint,.val .uint,.val .uint,.val .uint,.mem bytesR,.alias bytesR] .uint :=
      match p with | .legacy => .simple (.local .here) | .viaIR => .simple (.local (.there .here))
    let right : Idx [.val .uint,.val .uint,.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.val .uint) :=
      match p with | .legacy => .there .here | .viaIR => .here
    match (castValue 8 left).evalT o.st with
    | .ok x => some (x.val,(TEnv.get right o.st.env).val,(TEnv.get (.there (.there (.there .here))) o.st.env).val)
    | _ => none
  | _ => none
/-- info: [some (1, 7, 257), some (1, 257, 257), some (1, 7, 257), some (1, 257, 257)] -/
#guard_msgs in
#eval IO.println (reprStr [sourcePair .legacy,sourcePair .viaIR,targetPair .legacy,targetPair .viaIR])

-- Wrong stale capture7, omitted narrowing257 and narrowed caller1 are rejected.
example : sourcePair .legacy ≠ some (7,7,257) := by decide
example : sourcePair .viaIR ≠ some (257,257,257) := by decide
example : targetPair .legacy ≠ some (1,7,1) := by decide
example : targetPair .viaIR ≠ targetPair .legacy := by decide

-- Execute the wrong stale local and omitted conversion, rather than only naming them.
/-- info: [some 7, some 257, some 1] -/
#guard_msgs in
#eval IO.println (reprStr [
  match (castValue 8 (.simple (.local (.there .here)))).evalT tgt with
    | .ok v => some v.val | _ => none,
  match (assignLocalOperand (.there .here) .here).run tgt with
    | .ok (_, .prim v) => some v.val | _ => none,
  match (assignedOperand 8 (.there .here) .here).run tgt with
    | .ok (_, .prim v) => some v.val | _ => none])

def out := tgt.setLocal (.there .here) (integerValue .u256 257 (by decide))
example : out.heap = tgt.heap ∧ out.glob = tgt.glob ∧
    TEnv.get (.there (.there .here)) out.env = TEnv.get (.there (.there .here)) tgt.env ∧
    TEnv.get (.there (.there (.there .here))) out.env = some storageRef := ⟨rfl,rfl,rfl,rfl⟩
example : ∃ r : HRef tgt.H bytesR,
    TEnv.get (.there (.there .here)) tgt.env = some r ∧ tgt.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory

end Solidity.Lowering.V07.UnsignedCastControls
