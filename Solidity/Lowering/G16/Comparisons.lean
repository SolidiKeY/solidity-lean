import Solidity.Lowering.V07.BooleanComparisons
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

/-- Assignment/read comparisons for every numeric-key Source type, target width/sign and comparison opcode.
Initial reads derive both pipeline orders and exact caller writes; no frontend or arbitrary-effects claim. -/
theorem assignment_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    {τ : Source.STy} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy)
    (op : BinOp) (accepts : op.accepts .uint = true) (returns : op.ret .uint = .bool)
    (i a : Source.Idx srcΓ τ) (c d : Idx Γ (.val (integerPrim t)))
    (v w : Source.Val E.layout τ) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : source.1.get a = v) (readI : source.1.get i = w)
    (keyA : v.key = some x) (keyI : w.key = some y)
    (nativeA : TEnv.get d target.env = integerValue t x hx)
    (nativeI : TEnv.get c target.env = integerValue t y hy) :
    ∃ result : Bool,
      Source.cmpVal (NumericComparisons.sourceOp op) v
        (if G.pipeline = Roadmap.Pipeline.legacy then w else v) = .ok result ∧
      (Source.evalE G F (fuel+4)
        (.compare (NumericComparisons.sourceOp op) (.assign (.local i) (.local a)) (.local i))).run source =
        (.ok (.val (.bool result)),(source.1.set i v,source.2)) ∧
      (NumericComparisons.operand t op accepts returns G.pipeline c d).run target =
        .ok (⟨target.setLocal c (integerValue t x hx),List.prefix_refl _⟩,.prim result) := by
  obtain ⟨result,numeric,native⟩ := NumericComparisons.operand_run (D := E.layout)
    target t op accepts returns G.pipeline c d x y hx hy nativeA nativeI
  have computed : Source.cmpVal (NumericComparisons.sourceOp op) v
      (if G.pipeline = Roadmap.Pipeline.legacy then w else v) = .ok result := by
    by_cases order : G.pipeline = Roadmap.Pipeline.legacy
    · simpa only [Source.cmpVal,keyA,keyI,Source.Val.key,LessThan.rightAt,if_pos order] using numeric
    · simpa only [Source.cmpVal,keyA,Source.Val.key,LessThan.rightAt,if_neg order] using numeric
  have pair := source_assign_read_pair G F fuel source i a v w readA readI
  refine ⟨result,computed,?_,native⟩
  rw [Source.evalE,Source.Hoare.run_bind,pair]
  change (do let answer ← Source.EM.lift (Source.cmpVal (NumericComparisons.sourceOp op) v
                (if G.pipeline = Roadmap.Pipeline.legacy then w else v))
             pure (Source.RVal.val (.bool answer))).run (source.1.set i v,source.2) = _
  rw [computed]
  rfl

end Solidity.Lowering.G16.Comparisons

/-- info: 'Solidity.Lowering.G16.Comparisons.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Comparisons.transport

/-- info: 'Solidity.Lowering.G16.Comparisons.assignment_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Comparisons.assignment_transport

namespace Solidity.Lowering.G16.BooleanComparison

/-- Boolean equality/inequality from initial reads, including pipeline-dependent assignment capture and exact writes. This leaf does not associate frontend output or arbitrary effects. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (ne : Bool)
    (i a : Source.Idx srcΓ .bool) (j b : Idx Γ (.val .bool)) (x y : Bool)
    (readA : source.1.get a = .bool x) (readI : source.1.get i = .bool y)
    (nativeA : TEnv.get b target.env = x) (nativeI : TEnv.get j target.env = y) :
    (Source.evalE G F (fuel+4)
      (.compare (V07.BooleanComparisons.sourceOp ne)
        (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (.bool (V07.BooleanComparisons.answer ne x
        (if G.pipeline = .legacy then y else x)))),(source.1.set i (.bool x),source.2)) ∧
    (V07.BooleanComparisons.operand ne G.pipeline j b).run target =
      .ok (⟨target.setLocal j x,List.prefix_refl _⟩,
        .prim (V07.BooleanComparisons.answer ne x (if G.pipeline = .legacy then y else x))) := by
  exact ⟨V07.BooleanComparisons.source_assignment G F fuel source ne i a x y readA readI,
    V07.BooleanComparisons.operand_run target ne G.pipeline j b x y nativeA nativeI⟩

end Solidity.Lowering.G16.BooleanComparison

/-- info: 'Solidity.Lowering.G16.BooleanComparison.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.BooleanComparison.transport
