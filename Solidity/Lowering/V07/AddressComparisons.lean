import Solidity.Lowering.V07.AddressConversions
import Solidity.Lowering.V07.NumericComparisons

/-! Address comparisons over the existing uint carrier. These operational
clauses do not provide frontend selection or a P8 admission inhabitant.
Canonical initial address agreement is required; arbitrary native high words
are not silently truncated. Scalar address equality is not heap alias identity. -/
namespace Solidity.Lowering.V07.AddressComparisons
open AddressConversions

theorem source_numeric {D : Source.Layout} (p : Bool) (op : Source.BinOp) (a b : Roadmap.Address) :
 Source.cmpVal op (.address a : Source.Val D (.address p)) (.address b) =
 Source.cmpVal op (.int a.val (address_range a) : Source.Val D (.int ty)) (.int b.val (address_range b)) := by
 rfl


theorem value_run {D : Source.Layout} {C : Contract} {Γ : Ctx}
    (target : State C Γ) (p : Bool) (op : BinOp)
    (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (a b : Roadmap.Address) (left right : Val C Γ .uint)
    (ha : left.evalT target = .ok (addressValue a))
    (hb : right.evalT target = .ok (addressValue b)) :
    ∃ result : Bool,
      Source.cmpVal (NumericComparisons.sourceOp op)
        (.address a : Source.Val D (.address p)) (.address b) = .ok result ∧
      (NumericComparisons.value ty op hu hr left right).evalT target = .ok result := by
  obtain ⟨result,computed,run⟩ := NumericComparisons.value_run (D := D) target ty op hu hr
    left right a.val b.val (address_range a) (address_range b) ha hb
  exact ⟨result,(source_numeric p _ a b).trans computed,run⟩

theorem source_from_pair {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (p : Bool) (op : Source.BinOp) (left right : Source.RExpr E Γ (.address p))
    (a b : Roadmap.Address) (result : Bool)
    (computed : Source.cmpVal op (.address a : Source.Val E.layout (.address p)) (.address b) = .ok result)
    (pair : (Source.evalPair G F fuel left right).run source =
      (.ok (.val (.address a),.val (.address b)),mid)) :
    (Source.evalE G F (fuel+1) (.compare op left right)).run source =
      (.ok (.val (.bool result)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,pair]
  change (do
    let v ← Source.EM.lift (Source.cmpVal op (.address a : Source.Val E.layout (.address p)) (.address b))
    pure (Source.RVal.val (.bool v))).run mid = _
  rw [computed]
  rfl

def rightAt (pipeline : Roadmap.Pipeline) (a b : Roadmap.Address) : Roadmap.Address :=
  if pipeline = .legacy then b else a

theorem source_assignment {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (p : Bool) (op : Source.BinOp) (i r : Source.Idx Γ (.address p))
    (a b : Roadmap.Address) (result : Bool)
    (computed : Source.cmpVal op (.address a : Source.Val E.layout (.address p))
      (.address (rightAt G.pipeline a b)) = .ok result)
    (ha : source.1.get r = .address a) (hb : source.1.get i = .address b) :
    (Source.evalE G F (fuel+4) (.compare op (.assign (.local i) (.local r)) (.local i))).run source =
      (.ok (.val (.bool result)),(source.1.set i (.address a),source.2)) := by
  have pair := source_assign_read_pair G F fuel source i r (.address a) (.address b) ha hb
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true] at pair
    simp only [rightAt,order,if_true] at computed
    exact source_from_pair G F (fuel+3) source _ p op _ _ a b result computed pair
  · simp only [order,if_false] at pair
    simp only [rightAt,order,if_false] at computed
    exact source_from_pair G F (fuel+3) source _ p op _ _ a a result computed pair

theorem operand_run {D : Source.Layout} {C : Contract} {Γ : Ctx}
    (target : State C Γ) (p : Bool) (op : BinOp)
    (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (pipeline : Roadmap.Pipeline) (i r : Idx Γ (.val .uint)) (a b : Roadmap.Address)
    (ha : TEnv.get r target.env = addressValue a) (hb : TEnv.get i target.env = addressValue b) :
    ∃ result : Bool,
      Source.cmpVal (NumericComparisons.sourceOp op)
        (.address a : Source.Val D (.address p)) (.address (rightAt pipeline a b)) = .ok result ∧
      (NumericComparisons.operand ty op hu hr pipeline i r).run target =
        .ok (⟨target.setLocal i (addressValue a),List.prefix_refl _⟩,.prim result) := by
  obtain ⟨result,computed,run⟩ := NumericComparisons.operand_run (D := D) target ty op hu hr
    pipeline i r a.val b.val (address_range a) (address_range b) ha hb
  refine ⟨result,?_,run⟩
  cases pipeline <;> exact (source_numeric p _ _ _).trans computed

/-- Initial mapped values and binding identity derive both executions and the
entire reached context relation. No desired postcondition/run is a premise. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (p : Bool)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.address p)) (n : PrimTy.uint.Denote),
      R (.address p) (.val .uint) v n → AddressRel p v n)
    (i r : Source.Idx srcΓ (.address p)) (j k : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,k⟩)
    (a b : Roadmap.Address) (ha : source.1.get r = .address a) (hb : source.1.get i = .address b)
    (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool) :
    ∃ result : Bool,
      (Source.evalE G F (fuel+4) (.compare (NumericComparisons.sourceOp op)
        (.assign (.local i) (.local r)) (.local i))).run source =
          (.ok (.val (.bool result)),(source.1.set i (.address a),source.2)) ∧
      (NumericComparisons.operand ty op hu hr G.pipeline j k).run target =
        .ok (⟨target.setLocal j (addressValue a),List.prefix_refl _⟩,.prim result) ∧
      m.Related R (source.1.set i (.address a)) (TEnv.set j (addressValue a) target.env) := by
  have left := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned r k readMap)
  have right := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned i j writeMap)
  rw [ha] at left
  rw [hb] at right
  have readA := address_read p a _ left
  have readB := address_read p b _ right
  obtain ⟨result,computed,run⟩ := operand_run (D := E.layout) target p op hu hr G.pipeline j k a b readA readB
  have post : m.Related R (source.1.set i (source.1.get r))
      (TEnv.set j (TEnv.get k target.env) target.env) := ContextMap.related_assign m R source.1 target.env aligned i r j k writeMap readMap
  rw [ha,readA] at post
  exact ⟨result,source_assignment G F fuel source p _ i r a b result computed ha hb,run,post⟩
end Solidity.Lowering.V07.AddressComparisons

/-- info: 'Solidity.Lowering.V07.AddressComparisons.source_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisons.source_numeric

/-- info: 'Solidity.Lowering.V07.AddressComparisons.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisons.value_run

/-- info: 'Solidity.Lowering.V07.AddressComparisons.source_from_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisons.source_from_pair

/-- info: 'Solidity.Lowering.V07.AddressComparisons.source_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisons.source_assignment

/-- info: 'Solidity.Lowering.V07.AddressComparisons.operand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisons.operand_run

/-- info: 'Solidity.Lowering.V07.AddressComparisons.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressComparisons.transport
