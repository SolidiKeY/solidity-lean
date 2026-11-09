import Solidity.Lowering.V07.NumericComparisons

/-! Scalar comparisons through the existing numeric-key observation and V07's
six-opcode value program. The Source type remains intrinsic and unchanged:
nominally different Source types cannot be substituted for either operand.
This is operational local-expression transport, not frontend selection. -/
namespace Solidity.Lowering.G16.Comparisons
open Solidity.Lowering.V07

/-- One comparison family over every Source value type with numeric keys,
every valid target integer width/sign, and all six comparison opcodes.
Key and read premises observe initial values, not results or executions. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    {τ : Source.STy} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy)
    (op : BinOp) (accepts : op.accepts .uint = true) (returns : op.ret .uint = .bool)
    (a b : Source.Idx srcΓ τ) (c d : Idx Γ (.val (integerPrim t)))
    (v w : Source.Val E.layout τ) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : source.1.get a = v) (readB : source.1.get b = w)
    (keyA : v.key = some x) (keyB : w.key = some y)
    (nativeA : TEnv.get c target.env = integerValue t x hx)
    (nativeB : TEnv.get d target.env = integerValue t y hy) :
    ∃ result : Bool,
      (Source.evalE G F (fuel+3)
        (.compare (NumericComparisons.sourceOp op) (.local a) (.local b))).run source =
        (.ok (.val (.bool result)),source) ∧
      (NumericComparisons.value t op accepts returns (.simple (.local c)) (.simple (.local d))).evalT target = .ok result := by
  obtain ⟨result,numeric,run⟩ := NumericComparisons.value_run (D := E.layout)
    target t op accepts returns (.simple (.local c)) (.simple (.local d)) x y hx hy
      (congrArg Except.ok nativeA) (congrArg Except.ok nativeB)
  have computed : Source.cmpVal (NumericComparisons.sourceOp op) v w = .ok result := by
    simpa only [Source.cmpVal,keyA,keyB,Source.Val.key] using numeric
  have leftRun : (Source.evalE G F (fuel+1) (.local a)).run source = (.ok (.val v),source) := by
    change (Except.ok (Source.RVal.val (source.1.get a)),source) = _
    rw [readA]
  have rightRun : (Source.evalE G F (fuel+1) (.local b)).run source = (.ok (.val w),source) := by
    change (Except.ok (Source.RVal.val (source.1.get b)),source) = _
    rw [readB]
  have pair := source_pure_pair G F (fuel+1) source (.local a) (.local b)
    (.val v) (.val w) leftRun rightRun
  refine ⟨result,?_,run⟩
  rw [Source.evalE,Source.Hoare.run_bind,pair]
  change (do
    let answer ← Source.EM.lift (Source.cmpVal (NumericComparisons.sourceOp op) v w)
    pure (Source.RVal.val (.bool answer))).run source = _
  rw [computed]
  rfl

end Solidity.Lowering.G16.Comparisons

/-- info: 'Solidity.Lowering.G16.Comparisons.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Comparisons.transport
