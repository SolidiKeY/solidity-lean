import Solidity.Lowering.V07.IntegralRationalConstants
import Solidity.Lowering.V07.WordCastControls
import Solidity.Lowering.V07.UnsignedCasts

namespace Solidity.Lowering.V07.IntegralRationalControls
open IntegralRationalConstants Source.SemanticsExamples
open MixedAssignmentControls (C E globals)
open WordCastControls (si ti)
def q : Source.Q := ⟨6,2,by decide⟩
def src := WordCastControls.source .u8 2 9 (by decide) (by decide)
def tgt := WordCastControls.target .u8 2 9 (by decide) (by decide)
def initial := WordCastControls.initial .u8 2 9 (by decide) (by decide)
def allowed_client := allowed E q .u8 (by decide)
def numerator_client := numerator q (by decide)
def eqv_client := eqv_integer q (by decide)
def value_client := source_value (D := E.layout) q .u8 (by decide)
def source_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_run (globals p) {F0 with checked := checked} fuel src q .u8 (by decide)
def transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel src tgt q .u8 (by decide)
def assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_assignment (globals p) {F0 with checked := checked} fuel src q .u8 .here (by decide)
def assignment_transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  assignment_transport (globals p) {F0 with checked := checked} fuel src tgt q .u8 (by decide)
    (si .u8) (ti .u8) initial true
def fractional_client := fractional_refused (D := E.layout) ⟨3,2,by decide⟩ .u8 (by decide)
def outside_client := integral_outside_refused (D := E.layout) ⟨512,2,by decide⟩ .u8 (by decide) (by decide)
def not_allowed_client := not_allowed E ⟨3,2,by decide⟩ .u8 (by decide)
def pure_extension_client := DeferredSource.Operand.run_wk
  (IntegerConstants.operand .u8 q.toInt (by decide) : DeferredSource.Operand C
    [.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.prim .uint))
  (Thin.drop (t := .val .bool) .refl) tgt (true,tgt.env)
def assignment_extension_client := DeferredSource.Operand.run_wk
  (IntegerConstantAssignment.operand .u8 .here q.toInt (by decide) : DeferredSource.Operand C
    [.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.prim .uint))
  (Thin.drop (t := .val .bool) .refl) tgt (true,tgt.env)
def repeated_client (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport (globals p) F0 fuel src tgt q .u8 (by decide)
    (fun k : Fin 3 => si .u8 (decide (k.val < 2))) (fun k : Fin 3 => ti .u8 (decide (k.val < 2)))
    (initial.reindex (fun k : Fin 3 => decide (k.val < 2))) 0
def equal_content_client (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport (globals p) F0 fuel
    (WordCastControls.source .u8 2 2 (by decide) (by decide))
    (WordCastControls.target .u8 2 2 (by decide) (by decide)) q .u8 (by decide) (si .u8) (ti .u8)
    (WordCastControls.initial .u8 2 2 (by decide) (by decide)) true

def observe (p : Roadmap.Pipeline) (checked : Bool) (t : Source.IntTy) (r : Source.Q)
    (h : r.FitsInt t) (h0 : t.lo ≤ 0 ∧ 0 ≤ t.hi) (h1 : t.lo ≤ 1 ∧ 1 ≤ t.hi) : Option (List Int) :=
  let source := WordCastControls.source t 0 1 h0 h1
  let target := WordCastControls.target t 0 1 h0 h1
  match (Source.evalE (globals p) {F0 with checked := checked} 2
      (.conv (.const r) (.inl (allowed E r t h)))).run source,
    (Source.evalE (globals p) {F0 with checked := checked} 3
      (.assign (.local .here) (.conv (.const r) (.inl (allowed E r t h))))).run source,
    (IntegerConstantAssignment.code t .here r.toInt h.2).run target,
    (IntegerConstants.operand t r.toInt h.2).run target,
    (IntegerConstantAssignment.operand t .here r.toInt h.2).run target with
  | (.ok (.val pureValue),_),(.ok (.val assigned),post),.ok cap,.ok (_,.prim pureResult),.ok (out,.prim result) => do
    let a ← pureValue.key
    let b ← assigned.key
    let c ← (post.1.get .here).key
    let d ← (post.1.get (.there .here)).key
    let e ← PrimTy.num? (TEnv.get .here cap.st.env)
    let f ← PrimTy.num? (TEnv.get (.there .here) cap.st.env)
    let g ← PrimTy.num? (TEnv.get (.there (.there .here)) cap.st.env)
    let h ← PrimTy.num? pureResult
    let i ← PrimTy.num? result
    let j ← PrimTy.num? (TEnv.get .here out.st.env)
    let k ← PrimTy.num? (TEnv.get (.there .here) out.st.env)
    pure [a,b,c,d,e,f,g,h,i,j,k]
  | _,_,_,_,_ => none

def factors : List {d : Nat // 0 < d} := [⟨1,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨17,by decide⟩]
def check (p : Roadmap.Pipeline) (checked : Bool) (t : Source.IntTy) (z : Int)
    (factor : {d : Nat // 0 < d}) : Bool :=
  let r : Source.Q := ⟨z * factor.val,factor.val,factor.property⟩
  if h : r.FitsInt t then
    if h0 : t.lo ≤ 0 ∧ 0 ≤ t.hi then
      if h1 : t.lo ≤ 1 ∧ 1 ≤ t.hi then
        observe p checked t r h h0 h1 == some [z,z,z,1,z,z,1,z,z,z,1]
      else false
    else false
  else false
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.range 257).all fun bits =>
  if width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then [false,true].all fun signed =>
    let t : Source.IntTy := ⟨signed,bits,width⟩
    [Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
      [0,1,t.lo,t.hi].all fun z => factors.all fun factor => check p checked t z factor
  else true))

/-- info: [some [3, 3, 3, 1, 3, 3, 1, 3, 3, 3, 1], some [3, 3, 3, 1, 3, 3, 1, 3, 3, 3, 1]] -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].map fun p =>
  observe p true .u8 q (by decide) (by decide) (by decide)))

-- Dropping the denominator writes the numerator six, rather than the rational's value three.
/-- info: [some (3, 3), some (6, 6)] -/
#guard_msgs in
#eval IO.println (reprStr ([q.toInt,q.num].map fun n =>
  if h : Source.IntTy.u8.lo ≤ n ∧ n ≤ Source.IntTy.u8.hi then
    match (IntegerConstantAssignment.operand .u8 .here n h).run tgt with
    | .ok (out,.prim result) => some (result.val,(TEnv.get .here out.st.env).val)
    | _ => none
  else none))

-- A non-integral negative rational is refused, not silently floored or truncated toward zero.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let r : Source.Q := ⟨-3,2,by decide⟩
  let t : Source.IntTy := ⟨true,8,by decide⟩
  match Source.constVal r (.int t) (D := E.layout),
      (IntegerConstants.operand t r.toInt (by decide)).run tgt with
  | .error (.stuck why),.ok (_,.prim wrong) => why == "fractional constant at an integer type" &&
      PrimTy.num? wrong == some (-2) && r.trunc == -1 &&
      !(Source.STy.rational r).implicit E.isBase E.mapFree (.int t)
  | _,_ => false))

-- The integral quotient 256 is out of range for uint8; unchecked target truncation is a wrong conversion.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let r : Source.Q := ⟨512,2,by decide⟩
  match Source.constVal r (.int .u8) (D := E.layout),
      (UnsignedCasts.castValue 8 (IntegerConstants.value .u256 r.toInt (by decide))).evalT tgt with
  | .error (.stuck why),.ok wrong => why == "integer out of range" && wrong.val == 0 &&
      !(Source.STy.rational r).implicit E.isBase E.mapFree (.int .u8)
  | _,_ => false))
/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.allowed_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.allowed_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.numerator_client' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.numerator_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.eqv_client' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.eqv_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.value_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.value_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.source_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.transport_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.assignment_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.assignment_transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.assignment_transport_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.fractional_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.fractional_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.outside_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.outside_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.not_allowed_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.not_allowed_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.pure_extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.pure_extension_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.assignment_extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.assignment_extension_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.repeated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.repeated_client

/-- info: 'Solidity.Lowering.V07.IntegralRationalControls.equal_content_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalControls.equal_content_client

end Solidity.Lowering.V07.IntegralRationalControls
