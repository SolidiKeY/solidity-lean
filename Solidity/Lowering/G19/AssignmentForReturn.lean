import Solidity.Lowering.G19.AssignmentForContinue

/-! Mapped for-loop condition with an immediate bare return. The arbitrary
post is unreachable on both condition outcomes. V07 relation and code only. -/
namespace Solidity.Lowering.G19.AssignmentForReturn
open Solidity.Lowering.V07
open AssignmentReturnFlag

def statement {E : Source.Env} {srcΓ : Source.RCtx} {M l u : Bool}
    (i a : Source.Idx srcΓ .bool) (post : Source.ROptExpr E srcΓ) :
    Source.RStmt E [] M ⟨l,u⟩ srcΓ srcΓ :=
  .forLoop .skip (.some (.assign (.local i) (.local a))) post (.ret rfl)

theorem iter_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (choice : Bool) (read : ls.get a = .bool choice)
    (post : Source.ROptExpr E srcΓ) :
    (Source.forIter G F (fuel+3) nps ph (R := []) (M := M) (u := u)
      (.some (.assign (.local i) (.local a))) post (.ret rfl) ls).run (.nil,st) =
      (.ok (if choice then Source.Out.ret (ls.set i (.bool choice))
        else Source.Out.normal (ls.set i (.bool choice))),(.nil,st)) := by
  cases choice
  all_goals
    rw [Source.forIter,Source.Hoare.run_bind,
      AssignmentWhileReset.condition_sub G F fuel ls st i a _ read]
    rfl

theorem source_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M l u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (choice : Bool) (read : ls.get a = .bool choice)
    (post : Source.ROptExpr E srcΓ) :
    (Source.execS G F (fuel+4) nps ph (M := M)
      (statement (l := l) (u := u) i a post) ls).run (.nil,st) =
      (.ok (if choice then Source.Out.ret (ls.set i (.bool choice))
        else Source.Out.normal (ls.set i (.bool choice))),(.nil,st)) := by
  have initRun : (Source.execS G F (fuel+3) nps ph (R := []) (M := M)
      (k := ⟨true,u⟩) .skip ls).run (.nil,st) = (.ok (Source.Out.normal ls),(.nil,st)) := rfl
  dsimp only [statement,Source.execS]
  apply AssignmentForContinue.bind_result initRun
  dsimp only
  apply AssignmentForContinue.bind_result (iter_run G F fuel nps ph ls st i a choice read post)
  cases choice <;> simp only [AssignmentWhileReset.restore_self] <;> rfl

theorem source_zero {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {M l u : Bool} (ls : Source.Locals E.layout srcΓ)
    (i a : Source.Idx srcΓ .bool) (post : Source.ROptExpr E srcΓ) :
    Source.execS G F 0 nps ph (M := M)
      (statement (l := l) (u := u) i a post) ls =
      Source.EM.halt .timeout := by rfl


/-- A map-guided one-shape lowering endpoint; the post has no execution premise. -/
theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat)
    (ph : Option (Source.Ph E)) {M l u : Bool}
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      R .bool (.val .bool) v b → v = .bool b)
    (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (map_i : m.slot i = ⟨.val .bool,boolSlot m i hi⟩)
    (map_a : m.slot a = ⟨.val .bool,boolSlot m a ha⟩)
    (post : Source.ROptExpr E srcΓ) :
    (Source.execS G F (fuel+4) nps ph (M := M)
      (statement (l := l) (u := u) i a post) source.1).run (.nil,source.2) =
      (.ok (if (TEnv.get (boolSlot m a ha) target.env : Bool) = true then
        Source.Out.ret (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))
        else Source.Out.normal (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))),
        (.nil,source.2)) ∧
    (code m i a hi ha : Prog C Γ (.val .bool :: Γ)).run target =
      .ok ⟨reached m i a hi ha target,List.prefix_refl _⟩ ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R
      (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))
      (reached m i a hi ha target).env ∧
    TEnv.get .here (reached m i a hi ha target).env = TEnv.get (boolSlot m a ha) target.env ∧
    (reached m i a hi ha target).glob = target.glob := by
  have reflected : source.1.get a = .bool (TEnv.get (boolSlot m a ha) target.env) :=
    boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned a _ map_a)
  rcases condition_assignment_transport G F fuel source target m R aligned
    boolReflect i a (boolSlot m i hi) (boolSlot m a ha) map_i map_a with
    ⟨_,targetRun,_,related,globals⟩
  exact ⟨source_run G F fuel nps ph source.1 source.2 i a _ reflected post,
    targetRun,related,rfl,globals⟩

end Solidity.Lowering.G19.AssignmentForReturn
