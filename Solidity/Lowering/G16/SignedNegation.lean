import Solidity.Lowering.G16.PanicGuard
import Solidity.Lowering.V07.SignedNegation
import Solidity.Lowering.V07.IntegerConstants

/-! Signed negation at every valid width, including checked minimum-value
panic. Source typing admits integer negation only at signed types
(`Source/ExpressionTyping.lean`, `Typed.neg`). V07 supplies the wrapping
value program; the new guard preserves the actual arithmetic panic bytes. -/
namespace Solidity.Lowering.G16.SignedNegation
open Solidity.Lowering.V07
open SignedWidthCasts (ty)

private theorem hi_eq (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (ty bits valid).hi = -(ty bits valid).lo - 1 := by
  have positive : (0 : Nat) < 2 ^ (bits-1) := Source.two_pow_pos (bits-1)
  change (((2 ^ (bits-1) - 1 : Nat) : Int)) = -(-((2 ^ (bits-1) : Nat) : Int)) - 1
  omega

private theorem neg_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) :
    ((ty bits valid).lo ≤ -x ∧ -x ≤ (ty bits valid).hi) ↔ x ≠ (ty bits valid).lo := by
  have symmetry : (ty bits valid).hi = -(ty bits valid).lo - 1 := hi_eq bits valid
  omega

private theorem min_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (ty bits valid).lo ≤ (ty bits valid).lo ∧ (ty bits valid).lo ≤ (ty bits valid).hi := by
  have zero : (ty bits valid).lo ≤ 0 ∧ 0 ≤ (ty bits valid).hi := integer_zero_range (ty bits valid)
  exact ⟨Int.le_refl _,Int.le_trans zero.1 zero.2⟩

def condition {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (j : Idx Γ (.val .int)) : Val C Γ .bool :=
  .binop .neB rfl rfl (.simple (.local j))
    (IntegerConstants.value (ty bits valid) (ty bits valid).lo (min_range bits valid))

private theorem condition_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (j : Idx Γ (.val .int)) (x : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : TEnv.get j target.env = integerValue (ty bits valid) x hx) :
    (condition bits valid j).evalT target = .ok (decide (x ≠ (ty bits valid).lo)) := by
  change TRes.ofOpt (BinOp.evalT .neB rfl (TEnv.get j target.env)
    (integerValue (ty bits valid) (ty bits valid).lo (min_range bits valid))) = _
  rw [read]
  simp only [decide_not]
  rfl

def guardPrefix {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (checked : Bool)
    (j : Idx Γ (.val .int)) : Prog C Γ Γ :=
  if checked then .cons (PanicGuard.code .arithmetic (condition bits valid j)) .nil else .nil

def operand {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (checked : Bool)
    (j : Idx Γ (.val .int)) : DeferredSource.Operand C Γ (.prim .int) :=
  ⟨Γ,guardPrefix bits valid checked j,
    .val (Solidity.Lowering.V07.SignedNegation.negValue bits (.simple (.local j)))⟩

private theorem prefix_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (checked : Bool)
    (j : Idx Γ (.val .int)) (x : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : TEnv.get j target.env = integerValue (ty bits valid) x hx) :
    (guardPrefix bits valid checked j).run target =
      if checked = true ∧ x = (ty bits valid).lo then
        .error (THalt.ofData (Source.panicData .arithmetic))
      else .ok (⟨target,List.prefix_refl _⟩ : Out C target.H Γ) := by
  cases checked with
  | false =>
    simp only [guardPrefix,Bool.false_eq_true,if_false,false_and,Prog.run_nil]
  | true =>
    by_cases minimum : x = (ty bits valid).lo
    · have test : (condition bits valid j).evalT target = .ok false := by
        simpa only [minimum,ne_eq,not_true_eq_false,decide_false] using
          condition_run target bits valid j x hx read
      have failed : (PanicGuard.code .arithmetic (condition bits valid j)).run target =
          .error (THalt.ofData (Source.panicData .arithmetic)) :=
        PanicGuard.run target .arithmetic (condition bits valid j) false test
      simp only [guardPrefix,if_true,true_and,if_pos minimum]
      change TRun.seq (PanicGuard.code .arithmetic (condition bits valid j)).runR _ target = _
      simp only [TRun.seq,show (PanicGuard.code .arithmetic (condition bits valid j)).runR target =
        .error (THalt.ofData (Source.panicData .arithmetic)) from failed]
    · have test : (condition bits valid j).evalT target = .ok true := by
        simpa only [minimum,ne_eq,not_false_eq_true,decide_true] using
          condition_run target bits valid j x hx read
      have passed : (PanicGuard.code .arithmetic (condition bits valid j)).run target =
          .ok (⟨target,List.prefix_refl _⟩ : Out C target.H Γ) :=
        PanicGuard.run target .arithmetic (condition bits valid j) true test
      simp only [guardPrefix,if_true,true_and,if_neg minimum]
      rw [Prog.run_cons_ok passed,Prog.run_nil]
      all_goals rfl

private theorem value_source (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {D : Source.Layout} (checked : Bool) (x : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) :
    Source.unaryVal checked .neg (.int x hx : Source.Val D (.int (ty bits valid))) =
      if checked = true ∧ x = (ty bits valid).lo then
        .error (.revert (Source.panicData .arithmetic))
      else .ok (Source.intWrap (ty bits valid) (-x)) := by
  cases checked with
  | false =>
    simp only [Bool.false_eq_true,false_and,if_false]
    exact Solidity.Lowering.V07.SignedNegation.source_neg_unchecked bits valid x hx
  | true =>
    by_cases minimum : x = (ty bits valid).lo
    · have outside : ¬ ((ty bits valid).lo ≤ -x ∧ -x ≤ (ty bits valid).hi) := by
        intro bound
        exact ((neg_range bits valid x hx).mp bound) minimum
      simp only [true_and,if_pos minimum,Source.unaryVal,Source.intRes,
        dif_neg outside,if_true,Source.panic]
      all_goals rfl
    · have bound : (ty bits valid).lo ≤ -x ∧ -x ≤ (ty bits valid).hi :=
        (neg_range bits valid x hx).mpr minimum
      have wrapped : (ty bits valid).wrap (-x) = -x :=
        SignedNarrowing.wrap_of_range bits valid (-x) bound
      simp only [true_and,if_neg minimum,Source.unaryVal,Source.intRes,
        dif_pos bound,Source.intWrap,wrapped]
      all_goals rfl

private theorem source_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i : Source.Idx srcΓ (.int (ty bits valid))) (x : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : source.1.get i = .int x hx) :
    (Source.evalE G F (fuel+2) (.unary .neg (.local i))).run source =
      if F.checked = true ∧ x = (ty bits valid).lo then
        (.error (.revert (Source.panicData .arithmetic)),source)
      else (.ok (.val (Source.intWrap (ty bits valid) (-x))),source) := by
  have localRun : (Source.evalE G F (fuel+1) (.local i)).run source =
      (.ok (.val (.int x hx)),source) := by
    change (Except.ok (Source.RVal.val (source.1.get i)),source) = _
    rw [read]
  rw [Source.evalE,Source.Hoare.run_bind,localRun]
  change (do
    let value ← Source.EM.lift (Source.unaryVal F.checked .neg
      (.int x hx : Source.Val E.layout (.int (ty bits valid))))
    pure (Source.RVal.val value)).run source = _
  rw [value_source]
  by_cases bad : F.checked = true ∧ x = (ty bits valid).lo
  · simp only [if_pos bad]
    all_goals rfl
  · simp only [if_neg bad]
    all_goals rfl

private theorem operand_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (checked : Bool)
    (j : Idx Γ (.val .int)) (x : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : TEnv.get j target.env = integerValue (ty bits valid) x hx) :
    (operand bits valid checked j).run target =
      if checked = true ∧ x = (ty bits valid).lo then
        .error (THalt.ofData (Source.panicData .arithmetic))
      else .ok (⟨target,List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap (-x)) ((ty bits valid).wrap_mem (-x)))) := by
  unfold operand DeferredSource.Operand.run
  rw [prefix_run target bits valid checked j x hx read]
  by_cases bad : checked = true ∧ x = (ty bits valid).lo
  · simp only [if_pos bad]
    all_goals rfl
  · simp only [if_neg bad]
    rw [Ext.eq_of_depth (guardPrefix (C := C) bits valid checked j).ext Ext.refl]
    simp only [bind,Except.bind,Src.valueT]
    rw [Solidity.Lowering.V07.SignedNegation.value_run bits valid target
      (.simple (.local j)) x hx (congrArg Except.ok read)]
    all_goals rfl

/-- Both checked arithmetic panic and checked/unchecked success are included,
without a nonminimum premise or a desired result/execution assumption. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i : Source.Idx srcΓ (.int (ty bits valid))) (j : Idx Γ (.val .int))
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (sourceRead : source.1.get i = .int x hx)
    (targetRead : TEnv.get j target.env = integerValue (ty bits valid) x hx) :
    if F.checked = true ∧ x = (ty bits valid).lo then
      (Source.evalE G F (fuel+2) (.unary .neg (.local i))).run source =
        (.error (.revert (Source.panicData .arithmetic)),source) ∧
      (operand bits valid F.checked j).run target = .error (THalt.ofData (Source.panicData .arithmetic))
    else
      (Source.evalE G F (fuel+2) (.unary .neg (.local i))).run source =
        (.ok (.val (Source.intWrap (ty bits valid) (-x))),source) ∧
      (operand bits valid F.checked j).run target =
        .ok (⟨target,List.prefix_refl _⟩,
          .prim (integerValue (ty bits valid) ((ty bits valid).wrap (-x)) ((ty bits valid).wrap_mem (-x)))) ∧
      IntValueRel (ty bits valid) (Source.intWrap (ty bits valid) (-x) : Source.Val E.layout (.int (ty bits valid)))
        (integerValue (ty bits valid) ((ty bits valid).wrap (-x)) ((ty bits valid).wrap_mem (-x))) := by
  by_cases bad : F.checked = true ∧ x = (ty bits valid).lo
  · simp only [if_pos bad]
    exact ⟨by simpa only [if_pos bad] using source_run G F fuel source bits valid i x hx sourceRead,
      by simpa only [if_pos bad] using operand_run target bits valid F.checked j x hx targetRead⟩
  · simp only [if_neg bad]
    exact ⟨by simpa only [if_neg bad] using source_run G F fuel source bits valid i x hx sourceRead,
      by simpa only [if_neg bad] using operand_run target bits valid F.checked j x hx targetRead,
      integer_related _ _ _⟩

end Solidity.Lowering.G16.SignedNegation

/-- info: 'Solidity.Lowering.G16.SignedNegation.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.SignedNegation.transport
