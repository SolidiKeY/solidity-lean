import Solidity.Lowering.G19.AssignmentWhileBreak

/-! One mapped for-loop initializer followed by an immediate break.
The omitted condition enters the body and the arbitrary post expression is
skipped. Only existing Source syntax, V07 ContextMap and operand code are used. -/
namespace Solidity.Lowering.G19.AssignmentForBreak
open Solidity.Lowering.V07
open AssignmentReturnFlag (boolSlot)
open AssignmentWhileBreak (code reached target_run)

def statement {E : Source.Env} {srcΓ : Source.RCtx} {R : List Source.STy} {M l u : Bool}
    (i a : Source.Idx srcΓ .bool) (post : Source.ROptExpr E srcΓ) :
    Source.RStmt E R M ⟨l,u⟩ srcΓ srcΓ :=
  .forLoop (.expr (.assign (.local i) (.local a))) .none post .brk

/-- The initializer executes once; immediate break bypasses the arbitrary post. -/
theorem source_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M l u : Bool}
    (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (choice : Bool) (read : ls.get a = .bool choice)
    (post : Source.ROptExpr E srcΓ) :
    (Source.execS G F (fuel+4) nps ph (R := R) (M := M)
      (statement (l := l) (u := u) i a post) ls).run (.nil,st) =
      (.ok (Source.Out.normal (ls.set i (.bool choice))),(.nil,st)) := by
  have hr : Source.evalE G F (fuel+2) (.assign (.local i) (.local a)) (plan := none) (ls,st) =
      (.ok (.val (.bool choice)),(ls.set i (.bool choice),st)) :=
    source_assign_local_run G F fuel (ls,st) i a (.bool choice) read
  have sub : (Source.EM.sub ls (Source.evalE G F (fuel+2)
      (.assign (.local i) (.local a)))).run (.nil,st) =
      (.ok (.val (.bool choice),ls.set i (.bool choice)),(.nil,st)) := by
    simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,hr]
  have initRun : (Source.execS G F (fuel+3) nps ph (R := R) (M := M)
      (k := ⟨true,u⟩) (.expr (.assign (.local i) (.local a))) ls).run (.nil,st) =
      (.ok (Source.Out.normal (ls.set i (.bool choice))),(.nil,st)) := by
    rw [Source.execS,Source.Hoare.run_bind,sub]
    rfl
  have iterRun : (Source.forIter G F (fuel+3) nps ph (R := R) (M := M)
      (u := u) .none post .brk (ls.set i (.bool choice))).run (.nil,st) =
      (.ok (Source.Out.normal (ls.set i (.bool choice))),(.nil,st)) := by rfl
  have restore : (ls.set i (.bool choice)).restore srcΓ = .ok (ls.set i (.bool choice)) := by
    unfold Source.Locals.restore
    generalize count : srcΓ.length - srcΓ.length = n
    have zero : n = 0 := by omega
    cases zero
    simp only [List.drop_zero, ↓reduceDIte, Source.Locals.drop]
    rfl
  rw [statement,Source.execS,Source.Hoare.run_bind,initRun]
  dsimp only
  rw [Source.Hoare.run_bind,iterRun]
  simp only [restore]
  rfl

theorem source_zero {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M l u : Bool} (ls : Source.Locals E.layout srcΓ)
    (i a : Source.Idx srcΓ .bool) (post : Source.ROptExpr E srcΓ) :
    Source.execS G F 0 nps ph (R := R) (M := M)
      (statement (l := l) (u := u) i a post) ls =
      Source.EM.halt .timeout := by rfl

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
    (map_a : m.slot a = ⟨.val .bool,boolSlot m a ha⟩)
    (post : Source.ROptExpr E srcΓ) :
    (Source.execS G F (fuel+4) nps ph (R := returns) (M := M)
      (statement (l := l) (u := u) i a post) source.1).run (.nil,source.2) =
      (.ok (Source.Out.normal (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))),
        (.nil,source.2)) ∧
    (code m i a hi ha : Prog C Γ Γ).run target =
      .ok ⟨reached m i a hi ha target,List.prefix_refl _⟩ ∧
    m.Related R (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))
      (reached m i a hi ha target).env ∧
    (reached m i a hi ha target).glob = target.glob := by
  have read : source.1.get a = .bool (TEnv.get (boolSlot m a ha) target.env) :=
    boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned a _ map_a)
  have related : m.Related R (source.1.set i (source.1.get a))
      (TEnv.set (boolSlot m i hi) (TEnv.get (boolSlot m a ha) target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i a
      (boolSlot m i hi) (boolSlot m a ha) map_i map_a
  rw [read] at related
  exact ⟨source_run G F fuel nps ph source.1 source.2 i a _ read post,
    target_run m i a hi ha target,related,rfl⟩

end Solidity.Lowering.G19.AssignmentForBreak
