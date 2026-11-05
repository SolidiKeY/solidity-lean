import Solidity.Lowering.V07.FixedBytesAssignment
import Solidity.Lowering.V07.NumericComparisons

/-! Actual fixed-byte comparisons with assignment/read effects. Captured values
follow the published pipeline; semantic comparison operands retain their roles. -/
namespace Solidity.Lowering.V07.FixedBytesComparisons

def rightAt (p : Roadmap.Pipeline) (xs ys : List UInt8) : List UInt8 := if p = .legacy then ys else xs

theorem right_length (p : Roadmap.Pipeline) (n : Nat) (xs ys : List UInt8)
    (hx : xs.length = n) (hy : ys.length = n) : (rightAt p xs ys).length = n := by
  cases p
  · exact hy
  · exact hx

theorem source_numeric {D : Source.Layout} (n : Nat) (w : 1 ≤ n ∧ n ≤ 32)
    (op : Source.BinOp) (xs ys : List UInt8) (hx : xs.length = n) (hy : ys.length = n) :
    Source.cmpVal op (.fixedBytes xs hx : Source.Val D (.fixedBytes n w)) (.fixedBytes ys hy) =
    Source.cmpVal op (.int (Source.bytesNat xs) (FixedBytesAssignment.range n w xs hx) : Source.Val D (.int .u256))
      (.int (Source.bytesNat ys) (FixedBytesAssignment.range n w ys hy)) := by
  rfl

theorem value_run {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (xs ys : List UInt8) (hx : xs.length = n) (hy : ys.length = n) (left right : Val C Γ .uint)
    (ha : left.evalT target = .ok (FixedBytesAssignment.value n w xs hx))
    (hb : right.evalT target = .ok (FixedBytesAssignment.value n w ys hy)) :
    ∃ result : Bool,
      Source.cmpVal (NumericComparisons.sourceOp op)
        (.fixedBytes xs hx : Source.Val D (.fixedBytes n w)) (.fixedBytes ys hy) = .ok result ∧
      (NumericComparisons.value .u256 op hu hr left right).evalT target = .ok result := by
  obtain ⟨result,computed,run⟩ := NumericComparisons.value_run (D := D) target .u256 op hu hr left right
    (Source.bytesNat xs) (Source.bytesNat ys) (FixedBytesAssignment.range n w xs hx)
    (FixedBytesAssignment.range n w ys hy) ha hb
  exact ⟨result,(source_numeric n w _ xs ys hx hy).trans computed,run⟩

theorem source_from_pair {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (op : Source.BinOp) (left right : Source.RExpr E Γ (.fixedBytes n w))
    (xs ys : List UInt8) (hx : xs.length = n) (hy : ys.length = n) (result : Bool)
    (computed : Source.cmpVal op (.fixedBytes xs hx : Source.Val E.layout (.fixedBytes n w)) (.fixedBytes ys hy) = .ok result)
    (pair : (Source.evalPair G F fuel left right).run source = (.ok (.val (.fixedBytes xs hx),.val (.fixedBytes ys hy)),mid)) :
    (Source.evalE G F (fuel+1) (.compare op left right)).run source = (.ok (.val (.bool result)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,pair]
  change (do
    let v ← Source.EM.lift (Source.cmpVal op (.fixedBytes xs hx : Source.Val E.layout (.fixedBytes n w)) (.fixedBytes ys hy))
    pure (Source.RVal.val (.bool v))).run mid = _
  rw [computed]
  rfl

theorem source_assignment {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (op : Source.BinOp) (i r : Source.Idx Γ (.fixedBytes n w))
    (xs ys : List UInt8) (hx : xs.length = n) (hy : ys.length = n) (result : Bool)
    (computed : Source.cmpVal op (.fixedBytes xs hx : Source.Val E.layout (.fixedBytes n w))
      (.fixedBytes (rightAt G.pipeline xs ys) (right_length G.pipeline n xs ys hx hy)) = .ok result)
    (ha : source.1.get r = .fixedBytes xs hx) (hb : source.1.get i = .fixedBytes ys hy) :
    (Source.evalE G F (fuel+4) (.compare op (.assign (.local i) (.local r)) (.local i))).run source =
      (.ok (.val (.bool result)),(source.1.set i (.fixedBytes xs hx),source.2)) := by
  have pair := source_assign_read_pair G F fuel source i r (.fixedBytes xs hx) (.fixedBytes ys hy) ha hb
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true] at pair
    simp only [rightAt,order,if_true] at computed
    exact source_from_pair G F (fuel+3) source _ n w op _ _ xs ys hx hy result computed pair
  · simp only [order,if_false] at pair
    simp only [rightAt,order,if_false] at computed
    exact source_from_pair G F (fuel+3) source _ n w op _ _ xs xs hx hx result computed pair

theorem operand_run {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (p : Roadmap.Pipeline) (i r : Idx Γ (.val .uint)) (xs ys : List UInt8) (hx : xs.length = n) (hy : ys.length = n)
    (ha : TEnv.get r target.env = FixedBytesAssignment.value n w xs hx)
    (hb : TEnv.get i target.env = FixedBytesAssignment.value n w ys hy) :
    ∃ result : Bool,
      Source.cmpVal (NumericComparisons.sourceOp op)
        (.fixedBytes xs hx : Source.Val D (.fixedBytes n w))
        (.fixedBytes (rightAt p xs ys) (right_length p n xs ys hx hy)) = .ok result ∧
      (NumericComparisons.operand .u256 op hu hr p i r).run target =
        .ok (⟨target.setLocal i (FixedBytesAssignment.value n w xs hx),List.prefix_refl _⟩,.prim result) := by
  obtain ⟨result,computed,run⟩ := NumericComparisons.operand_run (D := D) target .u256 op hu hr p i r
    (Source.bytesNat xs) (Source.bytesNat ys) (FixedBytesAssignment.range n w xs hx)
    (FixedBytesAssignment.range n w ys hy) ha hb
  refine ⟨result,?_,run⟩
  cases p
  · exact (source_numeric n w _ xs ys hx hy).trans computed
  · exact (source_numeric n w _ xs xs hx hx).trans computed

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.fixedBytes n w)) (x : PrimTy.uint.Denote),
      R (.fixedBytes n w) (.val .uint) v x → FixedBytesAssignment.Rel n w v x)
    (i r : Source.Idx srcΓ (.fixedBytes n w)) (j k : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,k⟩)
    (xs ys : List UInt8) (hx : xs.length = n) (hy : ys.length = n)
    (ha : source.1.get r = .fixedBytes xs hx) (hb : source.1.get i = .fixedBytes ys hy)
    (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool) :
    ∃ result : Bool,
      (Source.evalE G F (fuel+4) (.compare (NumericComparisons.sourceOp op)
        (.assign (.local i) (.local r)) (.local i))).run source =
          (.ok (.val (.bool result)),(source.1.set i (.fixedBytes xs hx),source.2)) ∧
      (NumericComparisons.operand .u256 op hu hr G.pipeline j k).run target =
        .ok (⟨target.setLocal j (FixedBytesAssignment.value n w xs hx),List.prefix_refl _⟩,.prim result) ∧
      m.Related R (source.1.set i (.fixedBytes xs hx)) (TEnv.set j (FixedBytesAssignment.value n w xs hx) target.env) := by
  have left := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned r k readMap)
  have right := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned i j writeMap)
  rw [ha] at left
  rw [hb] at right
  have readA := FixedBytesAssignment.read_value n w xs hx _ left
  have readB := FixedBytesAssignment.read_value n w ys hy _ right
  obtain ⟨result,computed,run⟩ := operand_run (D := E.layout) target n w op hu hr G.pipeline j k xs ys hx hy readA readB
  have post : m.Related R (source.1.set i (source.1.get r))
      (TEnv.set j (TEnv.get k target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i r j k writeMap readMap
  rw [ha,readA] at post
  exact ⟨result,source_assignment G F fuel source n w _ i r xs ys hx hy result computed ha hb,run,post⟩
/-- info: 'Solidity.Lowering.V07.FixedBytesComparisons.right_length' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisons.right_length

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisons.source_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisons.source_numeric

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisons.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisons.value_run

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisons.source_from_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisons.source_from_pair

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisons.source_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisons.source_assignment

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisons.operand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisons.operand_run

/-- info: 'Solidity.Lowering.V07.FixedBytesComparisons.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesComparisons.transport

end Solidity.Lowering.V07.FixedBytesComparisons
