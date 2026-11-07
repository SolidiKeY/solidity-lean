import Solidity.Lowering.G19.AssignmentReturnFlag

/-! One effectful while shape: a Boolean local-assignment condition and an
immediate break body. The hand-written target program reuses V07's operand
through the existing G19 map projection; this is not a mapped lowering
endpoint. No new lowering relation, evaluator or source carrier. -/
namespace Solidity.Lowering.G19.AssignmentWhileBreak
open Solidity.Lowering.V07
open AssignmentReturnFlag (boolSlot)

/-- Drop only the existing fresh capture using an intrinsic scoped block. -/
def code {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) : Prog C Γ Γ :=
  .cons (.block (AssignmentReturnFlag.code m i a hi ha)) .nil

def reached {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (target : State C Γ) : State C Γ :=
  target.setLocal (boolSlot m i hi) (TEnv.get (boolSlot m a ha) target.env)

/-- The condition's caller-local write occurs even when it is false.
A true condition enters an immediate break, so there is no recursive turn. -/
theorem source_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M l u : Bool}
    (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (choice : Bool) (read : ls.get a = .bool choice) :
    (Source.execS G F (fuel+3) nps ph (R := R) (M := M)
      (.whileLoop (l := l) (u := u) (.assign (.local i) (.local a)) .brk) ls).run (.nil,st) =
      (.ok (Source.Out.normal (ls.set i (.bool choice))),(.nil,st)) := by
  have sub : (Source.EM.sub ls (Source.evalE G F (fuel+2)
      (.assign (.local i) (.local a)))).run (.nil,st) =
      (.ok (.val (.bool choice),ls.set i (.bool choice)),(.nil,st)) := by
    have hr : Source.evalE (plan := none) G F (fuel+2) (.assign (.local i) (.local a)) (ls,st) =
        (.ok (.val (.bool choice)),(ls.set i (.bool choice),st)) :=
      source_assign_local_run G F fuel (ls,st) i a (.bool choice) read
    simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,hr]
  rw [Source.execS,Source.Hoare.run_bind,sub]
  cases choice <;> rfl

theorem source_zero {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M l u : Bool} (ls : Source.Locals E.layout srcΓ)
    (i a : Source.Idx srcΓ .bool) :
    Source.execS G F 0 nps ph (R := R) (M := M)
      (.whileLoop (l := l) (u := u) (.assign (.local i) (.local a)) .brk) ls =
      Source.EM.halt .timeout := by rfl

/-- Actual scoped prefix execution, not an assumed loop simulation. -/
theorem target_run {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (target : State C Γ) :
    (code m i a hi ha : Prog C Γ Γ).run target =
      .ok ⟨reached m i a hi ha target,List.prefix_refl _⟩ := by
  have prefixRun : (AssignmentReturnFlag.code m i a hi ha : Prog C Γ (.val .bool :: Γ)).run target =
      .ok ⟨AssignmentReturnFlag.reached m i a hi ha target,List.prefix_refl _⟩ :=
    assigned_condition_prefix_run target (boolSlot m i hi) (boolSlot m a ha)
  unfold Prog.run at prefixRun
  have blockRun : (Stmt.block (AssignmentReturnFlag.code m i a hi ha) : Stmt C Γ Γ).run target =
      .ok ⟨reached m i a hi ha target,List.prefix_refl _⟩ := by
    show TRun.block (AssignmentReturnFlag.code m i a hi ha : Prog C Γ (.val .bool :: Γ)).ext
      (AssignmentReturnFlag.code m i a hi ha : Prog C Γ (.val .bool :: Γ)).runR target = _
    unfold TRun.block
    rw [prefixRun]
    rfl
  rw [code,Prog.run_cons_ok blockRun,Prog.run_nil]
  rfl

/-- One-shape mapped lowering endpoint. Initial value/position facts yield
actual Source/target runs plus reached alignment of every caller binding. -/
theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M l u : Bool}
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (v : LTy) → Source.Val E.layout τ → v.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      R .bool (.val .bool) v b → v = .bool b)
    (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (map_i : m.slot i = ⟨.val .bool,boolSlot m i hi⟩)
    (map_a : m.slot a = ⟨.val .bool,boolSlot m a ha⟩) :
    (Source.execS G F (fuel+3) nps ph (R := returns) (M := M)
      (.whileLoop (l := l) (u := u) (.assign (.local i) (.local a)) .brk) source.1).run (.nil,source.2) =
      (.ok (Source.Out.normal (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))),
        (.nil,source.2)) ∧
    (code m i a hi ha : Prog C Γ Γ).run target =
      .ok ⟨reached m i a hi ha target,List.prefix_refl _⟩ ∧
    m.Related R (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))
      (reached m i a hi ha target).env ∧
    (reached m i a hi ha target).glob = target.glob := by
  have read : source.1.get a = .bool (TEnv.get (boolSlot m a ha) target.env) :=
    boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned a _ map_a)
  have post : m.Related R (source.1.set i (source.1.get a))
      (TEnv.set (boolSlot m i hi) (TEnv.get (boolSlot m a ha) target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i a
      (boolSlot m i hi) (boolSlot m a ha) map_i map_a
  rw [read] at post
  exact ⟨source_run G F fuel nps ph source.1 source.2 i a _ read,
    target_run m i a hi ha target,post,rfl⟩

end Solidity.Lowering.G19.AssignmentWhileBreak
