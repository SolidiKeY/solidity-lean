import Solidity.Lowering.V07.SignedNarrowSubtraction
import Solidity.Lowering.V07.WordCastControls

namespace Solidity.Lowering.V07.SignedNegation
open SignedWidthCasts (ty)
def negValue {C : Contract} {Γ : Ctx} (bits : Nat) (v : Val C Γ .int) : Val C Γ .int :=
  SignedNarrowSubtraction.subValue bits (.simple (.lit 0 (by decide))) v

theorem source_neg_unchecked (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {D : Source.Layout} (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) :
    Source.unaryVal false .neg (.int x hx : Source.Val D (.int (ty bits valid))) =
      .ok (Source.intWrap (ty bits valid) (-x)) := by
  have h := SignedNarrowSubtraction.source_sub_unchecked bits valid (D := D) 0 x
    ((ty bits valid).wrap_mem 0) hx
  simpa only [Source.binVal,Source.intBin,Source.unaryVal,Int.zero_sub] using h

theorem value_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (v : Val C Γ .int)
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : v.evalT target = .ok (integerValue (ty bits valid) x hx)) :
    (negValue bits v).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (-x)) ((ty bits valid).wrap_mem (-x))) := by
  have h := SignedNarrowSubtraction.sub_value_run bits valid target (.simple (.lit 0 (by decide))) v
    0 x ((ty bits valid).wrap_mem 0) hx rfl read
  simpa only [negValue,Int.zero_sub] using h

theorem source_of_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source mid : Source.EMState E Γ) (e : Source.RExpr E Γ (.int (ty bits valid)))
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : (Source.evalE G {F with checked := false} fuel e).run source = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G {F with checked := false} (fuel+1) (.unary .neg e)).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (-x))),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  change (do
    let v ← Source.EM.lift (Source.unaryVal false .neg (.int x hx : Source.Val E.layout (.int (ty bits valid))))
    pure (Source.RVal.val v)).run mid = _
  rw [source_neg_unchecked]
  rfl

theorem source_local_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E Γ) (i : Source.Idx Γ (.int (ty bits valid)))
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : source.1.get i = .int x hx) :
    (Source.evalE G {F with checked := false} (fuel+2) (.unary .neg (.local i))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (-x))),source) := by
  apply source_of_run bits valid G F (fuel+1) source source (.local i) x hx
  change (Except.ok (Source.RVal.val (source.1.get i)),source) = _
  rw [read]

namespace Controls
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)
def src := WordCastControls.source (ty 8 (by decide)) (-128) 7 (by decide) (by decide)
def tgt := WordCastControls.target (ty 8 (by decide)) (-128) 7 (by decide) (by decide)
def source_value := source_neg_unchecked 8 (by decide) (D := E.layout) (-128) (by decide)
def target_value := value_run 8 (by decide) tgt (.simple (.local .here)) (-128) (by decide) rfl
def operand (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_of_run 8 (by decide) (globals p) F0 (fuel+1) src src (.local .here) (-128) (by decide) rfl
def source_local (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_local_run 8 (by decide) (globals p) F0 fuel src .here (-128) (by decide) rfl

def check (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (n : Int) : Bool :=
  let x := (ty bits valid).wrap n
  let hx := (ty bits valid).wrap_mem n
  let src := WordCastControls.source (ty bits valid) x 0 hx ((ty bits valid).wrap_mem 0)
  let tgt := WordCastControls.target (ty bits valid) x 0 hx ((ty bits valid).wrap_mem 0)
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 3 (.unary .neg (.local .here))).run src with
    | (.ok (.val v),_) => v.key | _ => none
  let tr := match (negValue bits (.simple (.local .here))).evalT tgt with
    | .ok v => some v.val | _ => none
  let q := (-x) % ((2^bits : Nat) : Int)
  let expected := if q < ((2^(bits-1) : Nat) : Int) then q else q-((2^bits : Nat) : Int)
  sr == some expected && tr == sr
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => (List.finRange 32).all fun i =>
  let bits := 8*(i.val+1)
  have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
  [(ty bits valid).lo,(ty bits valid).hi,-1,0,1].all (check p bits valid)))
/-- info: [some 128, some (-128)] -/
#guard_msgs in
#eval IO.println (reprStr [
  match (Val.unop .neg rfl rfl (.simple (.local .here))).evalT tgt with | .ok v => some v.val | _ => none,
  match (negValue 8 (.simple (.local .here))).evalT tgt with | .ok v => some v.val | _ => none])
/-- info: false -/
#guard_msgs in
#eval IO.println (reprStr (match Source.unaryVal true .neg
  (.int (-128) (by decide) : Source.Val E.layout (.int (ty 8 (by decide)))) with
  | .ok _ => true | _ => false))
end Controls
end Solidity.Lowering.V07.SignedNegation

/-- info: 'Solidity.Lowering.V07.SignedNegation.source_neg_unchecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegation.source_neg_unchecked

/-- info: 'Solidity.Lowering.V07.SignedNegation.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegation.value_run

/-- info: 'Solidity.Lowering.V07.SignedNegation.source_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegation.source_of_run

/-- info: 'Solidity.Lowering.V07.SignedNegation.source_local_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegation.source_local_run

/-- info: 'Solidity.Lowering.V07.SignedNegation.Controls.source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegation.Controls.source_value

/-- info: 'Solidity.Lowering.V07.SignedNegation.Controls.target_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegation.Controls.target_value

/-- info: 'Solidity.Lowering.V07.SignedNegation.Controls.operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegation.Controls.operand

/-- info: 'Solidity.Lowering.V07.SignedNegation.Controls.source_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegation.Controls.source_local
