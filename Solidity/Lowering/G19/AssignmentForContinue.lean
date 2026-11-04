import Solidity.Lowering.G19.AssignmentWhileContinue

/-! Continue in a for body skips its arbitrary suffix but executes the post
before the next mapped assignment condition. Existing V07 relation only. -/
namespace Solidity.Lowering.G19.AssignmentForContinue
open Solidity.Lowering.V07
open AssignmentReturnFlag (boolSlot)

def body {E : Source.Env} {srcΓ tailΓ : Source.RCtx} {R : List Source.STy} {M u : Bool}
    (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) : Source.RStmt E R M ⟨true,u⟩ srcΓ srcΓ :=
  .block (.stmt .cont tail)

def statement {E : Source.Env} {srcΓ tailΓ : Source.RCtx} {R : List Source.STy} {M l u : Bool}
    (i a : Source.Idx srcΓ .bool) (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    Source.RStmt E R M ⟨l,u⟩ srcΓ srcΓ :=
  .forLoop .skip (.some (.assign (.local i) (.local a)))
    (.some (.assign (.local a) (.bool false))) (body tail)

theorem pure_run {E : Source.Env} {Γ : Source.RCtx} {α : Type}
    (value : α) (state : Source.EMState E Γ) :
    (pure value : Source.EM E Γ α).run state = (.ok value,state) := by rfl

theorem bind_known {E : Source.Env} {Γ : Source.RCtx} {α β : Type}
    {m : Source.EM E Γ α} {before after : Source.EMState E Γ} {value : α}
    (completed : m.run before = (.ok value,after)) (next : α → Source.EM E Γ β) :
    (m >>= next).run before = (next value).run after := by
  rw [Source.Hoare.run_bind,completed]

theorem bind_result {E : Source.Env} {Γ : Source.RCtx} {α β : Type}
    {m : Source.EM E Γ α} {before after : Source.EMState E Γ} {value : α}
    (completed : m.run before = (.ok value,after)) (next : α → Source.EM E Γ β)
    {result : Except Source.Halt β × Source.EMState E Γ}
    (rest : (next value).run after = result) : (m >>= next).run before = result := by
  exact (bind_known completed next).trans rest

theorem bind_ext {E : Source.Env} {Γ : Source.RCtx} {α β : Type}
    (m : Source.EM E Γ α) (f g : α → Source.EM E Γ β)
    (same : ∀ value, f value = g value) : (m >>= f) = (m >>= g) := by
  exact congrArg (fun next => m >>= next) (funext same)

theorem bind_bool_ext {E : Source.Env} {Γ : Source.RCtx} {β : Type}
    (m : Source.EM E Γ (Source.Val E.layout .bool))
    (f g : Source.Val E.layout .bool → Source.EM E Γ β)
    (onFalse : f (.bool false) = g (.bool false))
    (onTrue : f (.bool true) = g (.bool true)) : (m >>= f) = (m >>= g) := by
  apply bind_ext
  intro value
  cases value with
  | bool b => cases b <;> assumption
  | memRef impossible _ => cases impossible
  | storRef impossible _ => cases impossible
  | cdRef impossible _ _ => cases impossible

theorem bind_out_ext {E : Source.Env} {Γ : Source.RCtx} {β : Type}
    (m : Source.EM E [] (Source.Out E.layout Γ Γ))
    (f g : Source.Out E.layout Γ Γ → Source.EM E [] β)
    (normal : ∀ ls, f (.normal ls) = g (.normal ls))
    (cont : ∀ ls, f (.cont ls) = g (.cont ls))
    (brk : ∀ ls, f (.brk ls) = g (.brk ls))
    (ret : ∀ ls, f (.ret ls) = g (.ret ls)) : (m >>= f) = (m >>= g) := by
  apply bind_ext
  intro outcome
  cases outcome with
  | normal ls => exact normal ls
  | cont ls => exact cont ls
  | brk ls => exact brk ls
  | ret ls => exact ret ls

theorem body_run {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    (Source.execS G F (fuel+4) nps ph (body tail) ls).run (.nil,st) =
      (.ok (Source.Out.cont ls),(.nil,st)) := by
  rw [body,Source.execS,Source.Hoare.run_bind,AssignmentWhileContinue.rest_run]
  rfl

theorem iter_false {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ)
    (read : ls.get a = .bool false) :
    (Source.forIter G F (fuel+3) nps ph (.some (.assign (.local i) (.local a)))
      (.some (.assign (.local a) (.bool false))) (body tail) ls).run (.nil,st) =
      (.ok (Source.Out.normal (ls.set i (.bool false))),(.nil,st)) := by
  rw [Source.forIter,Source.Hoare.run_bind,
    AssignmentWhileReset.condition_sub G F fuel ls st i a false read]
  rfl

theorem post_run {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    ((do
      let pair ← Source.EM.sub ls (Source.evalE G F (fuel+5) (.assign (.local a) (.bool false)))
      let next ← pure pair.2
      Source.forIter G F (fuel+5) nps ph (.some (.assign (.local i) (.local a)))
        (.some (.assign (.local a) (.bool false))) (body tail) next) :
      Source.EM E [] (Source.Out E.layout srcΓ srcΓ)).run (.nil,st) =
      (.ok (Source.Out.normal ((ls.set a (.bool false)).set i (.bool false))),(.nil,st)) := by
  rw [bind_known (AssignmentWhileReset.literal_sub G F (fuel+3) ls st a)]
  rw [bind_known (pure_run _ _)]
  exact iter_false G F (fuel+2) nps ph _ st i a tail (source_locals_get_set _ _ _)

theorem iter_unfold {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M u : Bool} (ls : Source.Locals E.layout srcΓ)
    (i a : Source.Idx srcΓ .bool) (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    Source.forIter G F (n+1) nps ph (.some (.assign (.local i) (.local a)))
      (.some (.assign (.local a) (.bool false))) (body tail) ls = (do
      let (go,l1) ← do
        let (cv,l1) ← Source.EM.sub ls (Source.evalE G F n (.assign (.local i) (.local a)))
        match ← Source.getV cv with
        | .bool b => pure (b,l1)
      if !go then return .normal l1
      let l2 ← match ← Source.execS G F n nps ph (body tail) l1 with
        | .normal l2 => Source.EM.lift (l2.restore srcΓ)
        | .cont l2 => pure l2
        | .brk l2 => return .normal l2
        | .ret l2 => return .ret l2
      let l3 ← do
        let pair ← Source.EM.sub l2 (Source.evalE G F n (.assign (.local a) (.bool false)))
        pure pair.2
      Source.forIter G F n nps ph (.some (.assign (.local i) (.local a)))
        (.some (.assign (.local a) (.bool false))) (body tail) l3) := by
  dsimp only [Source.forIter]
  apply bind_ext
  intro pair
  rcases pair with ⟨cv,l1⟩
  apply bind_bool_ext
  · split
    rename_i b2 same
    cases same
    rfl
  · split
    rename_i b2 same
    cases same
    apply bind_out_ext <;> intro ls <;> simp only


theorem iter_run {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (choice : Bool) (read : ls.get a = .bool choice)
    (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    (Source.forIter G F (fuel+6) nps ph (.some (.assign (.local i) (.local a)))
      (.some (.assign (.local a) (.bool false))) (body tail) ls).run (.nil,st) =
      (.ok (Source.Out.normal (AssignmentWhileReset.sourceAfter ls i a choice)),(.nil,st)) := by
  cases choice
  · exact iter_false G F (fuel+3) nps ph ls st i a tail read
  · apply Eq.trans (congrArg (fun action => action.run (.nil,st))
      (iter_unfold G F (fuel+5) nps ph ls i a tail))
    apply bind_result (AssignmentWhileReset.condition_sub G F (fuel+3) ls st i a true read)
    have getTrue : (Source.getV (.val (.bool true)) : Source.EM E [] (Source.Val E.layout .bool)).run
        (.nil,st) = (.ok (.bool true),(.nil,st)) := rfl
    apply bind_result getTrue
    apply bind_result (pure_run _ _)
    simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
    apply bind_result (pure_run _ _)
    apply bind_result (body_run G F (fuel+1) nps ph _ st tail)
    apply bind_result (pure_run _ _)
    exact post_run G F fuel nps ph _ st i a tail


theorem source_run {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M l u : Bool} (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (choice : Bool) (read : ls.get a = .bool choice)
    (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    (Source.execS G F (fuel+7) nps ph (statement (l := l) i a tail) ls).run (.nil,st) =
      (.ok (Source.Out.normal (AssignmentWhileReset.sourceAfter ls i a choice)),(.nil,st)) := by
  have initRun : (Source.execS G F (fuel+6) nps ph (R := R) (M := M) (k := ⟨true,u⟩)
      .skip ls).run (.nil,st) = (.ok (Source.Out.normal ls),(.nil,st)) := rfl
  rw [statement,Source.execS,Source.Hoare.run_bind,initRun]
  dsimp only
  rw [Source.Hoare.run_bind,iter_run G F fuel nps ph ls st i a choice read tail]
  simp only [AssignmentWhileReset.restore_self]
  rfl

theorem source_zero {E : Source.Env} {srcΓ tailΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M l u : Bool} (ls : Source.Locals E.layout srcΓ)
    (i a : Source.Idx srcΓ .bool) (tail : Source.RItems E R M ⟨true,u⟩ srcΓ tailΓ) :
    Source.execS G F 0 nps ph (statement (l := l) i a tail) ls = Source.EM.halt .timeout := by rfl

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
    (Source.execS G F (fuel+7) nps ph (R := returns) (M := M)
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

end Solidity.Lowering.G19.AssignmentForContinue
