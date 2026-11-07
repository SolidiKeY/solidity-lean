import Solidity.Lowering.V07.UdvtAssignment

/-! Boolean-underlying UDVT local assignment through existing typed values.
Source same-tag identity execution is reused; wrap/unwrap execution stays open. -/
namespace Solidity.Lowering.V07.UdvtBoolAssignment

def value {D : Source.Layout} (d : Source.DeclName) (underlying : D.underlying d = .bool)
    (b : Bool) : Source.Val D (.udvt d) :=
  .udvt (underlying.symm ▸ (.bool b : Source.Val D .bool))
def Rel {D : Source.Layout} (d : Source.DeclName) (underlying : D.underlying d = .bool)
    (source : Source.Val D (.udvt d)) (target : Bool) : Prop := source = value d underlying target

theorem value_key {D : Source.Layout} (d : Source.DeclName) (underlying : D.underlying d = .bool)
    (b : Bool) : (value d underlying b).key = some (if b then 1 else 0) := by
  change (underlying.symm ▸ (.bool b : Source.Val D .bool)).key = _
  rw [UdvtAssignment.key_cast]
  rfl

theorem value_related {D : Source.Layout} (d : Source.DeclName)
    (underlying : D.underlying d = .bool) (b : Bool) : Rel d underlying (value d underlying b) b := rfl

theorem read_value {D : Source.Layout} (d : Source.DeclName) (underlying : D.underlying d = .bool)
    (b n : Bool) (related : Rel d underlying (value d underlying b) n) : n = b := by
  have keys := congrArg Source.Val.key related
  rw [value_key,value_key] at keys
  cases b <;> cases n <;> first | rfl | cases keys

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (underlying : E.layout.underlying d = .bool)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.udvt d)) (n : Bool),
      R (.udvt d) (.val .bool) v n → Rel d underlying v n)
    (i r : Source.Idx srcΓ (.udvt d)) (j k : Idx Γ (.val .bool))
    (writeMap : m.slot i = ⟨.val .bool,j⟩) (readMap : m.slot r = ⟨.val .bool,k⟩)
    (b : Bool) (read : source.1.get r = value d underlying b) :
    (Source.evalE G F (fuel+3) (.conv (.assign (.local i) (.local r)) (Or.inr rfl))).run source =
      (.ok (.val (value d underlying b)),(source.1.set i (value d underlying b),source.2)) ∧
    (assignLocalOperand j k).run target =
      .ok (⟨target.setLocal j b,List.prefix_refl _⟩,.prim b) ∧
    Rel d underlying (value d underlying b) b ∧
    m.Related R (source.1.set i (value d underlying b)) (TEnv.set j b target.env) := by
  have point := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned r k readMap)
  rw [read] at point
  have targetRead := read_value d underlying b _ point
  have post : m.Related R (source.1.set i (source.1.get r))
      (TEnv.set j (TEnv.get k target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i r j k writeMap readMap
  rw [read,targetRead] at post
  exact ⟨UdvtAssignment.source_assignment G F fuel source d i r _ read,
    assign_local_operand_run target j k b targetRead,value_related d underlying b,post⟩
/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignment.value_key' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignment.value_key

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignment.value_related' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignment.value_related

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignment.read_value' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignment.read_value

/-- info: 'Solidity.Lowering.V07.UdvtBoolAssignment.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtBoolAssignment.transport

end Solidity.Lowering.V07.UdvtBoolAssignment
