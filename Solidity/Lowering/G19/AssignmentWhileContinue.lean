import Solidity.Lowering.G19.AssignmentWhileReset

/-! Continue after a donor reset skips an arbitrary body suffix and retests
an actual mapped while condition. Uses V07's existing ContextMap. -/
namespace Solidity.Lowering.G19.AssignmentWhileContinue
open Solidity.Lowering.V07
open AssignmentReturnFlag (boolSlot)

def body {E : Source.Env} {srcΓ tailΓ : Source.RCtx} {R : List Source.STy} {M u : Bool}
    (a : Source.Idx srcΓ .bool) (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    Source.RStmt E R M ⟨true,u⟩ srcΓ srcΓ :=
  .block (.stmt (.expr (.assign (.local a) (.bool false))) (.stmt .cont tail))

def statement {E : Source.Env} {srcΓ tailΓ : Source.RCtx} {R : List Source.STy} {M l u : Bool}
    (i a : Source.Idx srcΓ .bool) (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    Source.RStmt E R M ⟨l,u⟩ srcΓ srcΓ :=
  .whileLoop (.assign (.local i) (.local a)) (body a tail)

theorem rest_run {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    (Source.execItems G F (fuel+3) nps ph (.stmt .cont tail) ls).run (.nil,st) =
      (.ok (Source.Out.cont ls),(.nil,st)) := by rfl

theorem items_run {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (a : Source.Idx srcΓ .bool) (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    (Source.execItems G F (fuel+4) nps ph
      (.stmt (.expr (.assign (.local a) (.bool false))) (.stmt .cont tail)) ls).run (.nil,st) =
      (.ok (Source.Out.cont (ls.set a (.bool false))),(.nil,st)) := by
  rw [Source.execItems,Source.Hoare.run_bind,AssignmentWhileReset.source_body]
  dsimp only
  rw [Source.Hoare.run_bind,rest_run]
  simp only [Source.Out.up,AssignmentWhileReset.restore_self]
  rfl

theorem body_run {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (a : Source.Idx srcΓ .bool) (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    (Source.execS G F (fuel+5) nps ph (body a tail) ls).run (.nil,st) =
      (.ok (Source.Out.cont (ls.set a (.bool false))),(.nil,st)) := by
  rw [body,Source.execS,Source.Hoare.run_bind,items_run]
  rfl

theorem source_false {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M l u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ)
    (read : ls.get a = .bool false) :
    (Source.execS G F (fuel+3) nps ph (statement (l := l) i a tail) ls).run (.nil,st) =
      (.ok (Source.Out.normal (ls.set i (.bool false))),(.nil,st)) := by
  rw [statement,Source.execS,Source.Hoare.run_bind,
    AssignmentWhileReset.condition_sub G F fuel ls st i a false read]
  rfl

theorem source_run {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M l u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (choice : Bool) (read : ls.get a = .bool choice)
    (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    (Source.execS G F (fuel+8) nps ph (statement (l := l) i a tail) ls).run (.nil,st) =
      (.ok (Source.Out.normal (AssignmentWhileReset.sourceAfter ls i a choice)),(.nil,st)) := by
  rw [statement,Source.execS,Source.Hoare.run_bind,
    AssignmentWhileReset.condition_sub G F (fuel+5) ls st i a choice read]
  cases choice
  · rfl
  · have getTrue : (Source.getV (.val (.bool true)) : Source.EM E [] (Source.Val E.layout .bool)).run
        (.nil,st) = (.ok (.bool true),(.nil,st)) := rfl
    dsimp only
    rw [Source.Hoare.run_bind,getTrue]
    dsimp only
    rw [Source.Hoare.run_bind,body_run G F (fuel+2) nps ph]
    dsimp only
    exact source_false G F (fuel+4) nps ph _ st i a tail (source_locals_get_set _ _ _)

theorem source_zero {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M l u : Bool} (ls : Source.Locals E.layout srcΓ)
    (i a : Source.Idx srcΓ .bool) (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    Source.execS G F 0 nps ph (statement (l := l) i a tail) ls =
      Source.EM.halt .timeout := by rfl

theorem correct {E : Source.Env} {srcΓ tailΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M l u : Bool}
    (s : Source.EMState E srcΓ) (t : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (v : LTy) → Source.Val E.layout τ → v.TDenote C t.H → Prop)
    (aligned : m.Related R s.1 t.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool), R .bool (.val .bool) v b → v = .bool b)
    (falseValue : R .bool (.val .bool) (.bool false) false)
    (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (mapI : m.slot i = ⟨.val .bool,boolSlot m i hi⟩)
    (mapA : m.slot a = ⟨.val .bool,boolSlot m a ha⟩)
    (tail : Source.RItems E returns M ⟨true,u⟩ srcΓ tailΓ) :
    let choice : Bool := TEnv.get (boolSlot m a ha) t.env
    (Source.execS G F (fuel+8) nps ph (R := returns) (M := M)
      (statement (l := l) i a tail) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (AssignmentWhileReset.sourceAfter s.1 i a choice)),(.nil,s.2)) ∧
    (AssignmentWhileReset.code m i a hi ha : Prog C Γ Γ).run t =
      .ok ⟨AssignmentWhileReset.targetAfter m i a hi ha t,List.prefix_refl _⟩ ∧
    m.Related R (AssignmentWhileReset.sourceAfter s.1 i a choice) (AssignmentWhileReset.targetAfter m i a hi ha t).env ∧
    (AssignmentWhileReset.targetAfter m i a hi ha t).glob = t.glob := by
  dsimp only
  have read : s.1.get a = .bool (TEnv.get (boolSlot m a ha) t.env) :=
    boolReflect _ _ (ContextMap.value_at m R s.1 t.env aligned a _ mapA)
  exact ⟨source_run G F fuel nps ph s.1 s.2 i a _ read tail,
    (AssignmentWhileReset.correct G F fuel nps ph (returns := returns) (M := M) (l := l) (u := u)
      s t m R aligned boolReflect falseValue
      i a hi ha mapI mapA).2⟩

end Solidity.Lowering.G19.AssignmentWhileContinue
