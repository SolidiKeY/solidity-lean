import Solidity.Lowering.G19.AssignmentWhileBreak

/-! A mapped Boolean assignment condition whose body clears its donor.
The target uses the existing intrinsic loop; no new lowering relation. -/
namespace Solidity.Lowering.G19.AssignmentWhileReset
open Solidity.Lowering.V07
open AssignmentReturnFlag (boolSlot)

def body {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) : Prog C Γ Γ :=
  .cons (.assignLocal (boolSlot m a ha) (.simple (.bool false)))
    (AssignmentWhileBreak.code m i a hi ha)

def code {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) : Prog C Γ Γ :=
  .cons (.block (AssignmentWhileBreak.code m i a hi ha))
    (.cons (.loop .auto (.simple (.local (boolSlot m i hi))) (body m i a hi ha)) .nil)

def sourceAfter {D : Source.Layout} {srcΓ : Source.RCtx}
    (ls : Source.Locals D srcΓ) (i a : Source.Idx srcΓ .bool) (choice : Bool) :
    Source.Locals D srcΓ :=
  if choice then ((ls.set i (.bool choice)).set a (.bool false)).set i (.bool false)
    else ls.set i (.bool choice)

def targetAfter {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (t : State C Γ) : State C Γ :=
  let choice : Bool := TEnv.get (boolSlot m a ha) t.env
  let first := t.setLocal (boolSlot m i hi) choice
  {first with env := (if choice then TEnv.set (boolSlot m i hi) false
    (TEnv.set (boolSlot m a ha) false first.env) else first.env)}


theorem source_literal {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (ls : Source.Locals E.layout srcΓ) (st : Source.St E) (a : Source.Idx srcΓ .bool) :
    (Source.evalE G F (fuel+2) (.assign (.local a) (.bool false))).run (ls,st) =
      (.ok (.val (.bool false)),(ls.set a (.bool false),st)) := by rfl

theorem condition_sub {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (xs : Source.Locals E.layout srcΓ)
    (st : Source.St E) (i a : Source.Idx srcΓ .bool) (v : Bool) (read : xs.get a = .bool v) :
    (Source.EM.sub xs (Source.evalE G F (fuel+2) (.assign (.local i) (.local a)))).run (.nil,st) =
      (.ok (.val (.bool v),xs.set i (.bool v)),(.nil,st)) := by
  have h : Source.evalE G F (fuel+2) (.assign (.local i) (.local a)) (plan := none) (xs,st) =
      (.ok (.val (.bool v)),(xs.set i (.bool v),st)) := source_assign_local_run G F fuel (xs,st) i a _ read
  simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,h]

theorem literal_sub {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (xs : Source.Locals E.layout srcΓ)
    (st : Source.St E) (a : Source.Idx srcΓ .bool) :
    (Source.EM.sub xs (Source.evalE G F (fuel+2) (.assign (.local a) (.bool false)))).run (.nil,st) =
      (.ok (.val (.bool false),xs.set a (.bool false)),(.nil,st)) := by
  have h : Source.evalE G F (fuel+2) (.assign (.local a) (.bool false)) (plan := none) (xs,st) =
      (.ok (.val (.bool false)),(xs.set a (.bool false),st)) := source_literal G F fuel xs st a
  simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,h]

theorem source_body {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M : Bool} {k : Source.SCtx}
    (xs : Source.Locals E.layout srcΓ) (st : Source.St E) (a : Source.Idx srcΓ .bool) :
    (Source.execS G F (fuel+3) nps ph (R := returns) (M := M) (k := k)
      (.expr (.assign (.local a) (.bool false))) xs).run (.nil,st) =
      (.ok (Source.Out.normal (xs.set a (.bool false))),(.nil,st)) := by
  rw [Source.execS,Source.Hoare.run_bind,literal_sub]
  rfl

theorem source_false {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M l u : Bool}
    (xs : Source.Locals E.layout srcΓ) (st : Source.St E) (i a : Source.Idx srcΓ .bool)
    (read : xs.get a = .bool false) :
    (Source.execS G F (fuel+3) nps ph (R := returns) (M := M)
      (.whileLoop (l := l) (u := u) (.assign (.local i) (.local a))
        (.expr (.assign (.local a) (.bool false)))) xs).run (.nil,st) =
      (.ok (Source.Out.normal (xs.set i (.bool false))),(.nil,st)) := by
  rw [Source.execS,Source.Hoare.run_bind,condition_sub G F fuel xs st i a false read]
  rfl

theorem restore_self {D : Source.Layout} {srcΓ : Source.RCtx} (xs : Source.Locals D srcΓ) :
    xs.restore srcΓ = .ok xs := by
  unfold Source.Locals.restore
  generalize count : srcΓ.length - srcΓ.length = n
  have zero : n = 0 := by omega
  cases zero
  simp only [List.drop_zero, ↓reduceDIte, Source.Locals.drop]
  rfl

theorem source_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M l u : Bool}
    (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (choice : Bool) (read : ls.get a = .bool choice) :
    (Source.execS G F (fuel+4) nps ph (R := returns) (M := M)
      (.whileLoop (l := l) (u := u) (.assign (.local i) (.local a))
        (.expr (.assign (.local a) (.bool false)))) ls).run (.nil,st) =
      (.ok (Source.Out.normal (sourceAfter ls i a choice)),(.nil,st)) := by
  rw [Source.execS,Source.Hoare.run_bind,condition_sub G F (fuel+1) ls st i a choice read]
  cases choice
  · rfl
  · have getTrue : (Source.getV (.val (.bool true)) : Source.EM E [] (Source.Val E.layout .bool)).run
        (.nil,st) = (.ok (.bool true),(.nil,st)) := rfl
    dsimp only
    rw [Source.Hoare.run_bind,getTrue]
    dsimp only
    rw [Source.Hoare.run_bind,source_body G F fuel nps ph]
    dsimp only
    rw [restore_self]
    simp only [Source.EM.lift, Source.Hoare.run_bind]
    exact source_false G F fuel nps ph _ st i a (source_locals_get_set _ _ _)

theorem body_run {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) (t : State C Γ) :
    (body m i a hi ha : Prog C Γ Γ).run t =
      .ok ⟨(t.setLocal (boolSlot m a ha) false).setLocal (boolSlot m i hi) false,List.prefix_refl _⟩ := by
  have reset : (Stmt.assignLocal (boolSlot m a ha) (.simple (.bool false))).run t =
      .ok ⟨t.setLocal (boolSlot m a ha) false,List.prefix_refl _⟩ := rfl
  rw [body,Prog.run_cons_ok reset,AssignmentWhileBreak.target_run]
  change (Except.ok (⟨(t.setLocal (boolSlot m a ha) false).setLocal (boolSlot m i hi)
    (TEnv.get (boolSlot m a ha) (TEnv.set (boolSlot m a ha) false t.env)),List.prefix_refl _⟩ : Out C t.H Γ) :
      TRes (Out C t.H Γ)) = _
  rw [TEnv.get_set]


theorem run_reset_loop {α : Type} (step : α → TRes α) (test : α → TRes Bool)
    (first finish : α) (choice : Bool)
    (start : test first = .ok choice) (advance : step first = .ok finish)
    (stop : test finish = .ok false) :
    TLoop.run step test first = .ok (if choice then finish else first) := by
  cases choice
  · apply TLoop.run_of_iterN (n := 1)
    simp only [TLoop.iterN,TLoop.step,start]
    rfl
  · apply TLoop.run_of_iterN (n := 2)
    simp only [TLoop.iterN,TLoop.step,start,advance,stop]
    rfl

theorem loop_run {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) (t : State C Γ) :
    (Stmt.loop .auto (.simple (.local (boolSlot m i hi))) (body m i a hi ha)).run
      (t.setLocal (boolSlot m i hi) (TEnv.get (boolSlot m a ha) t.env)) =
      .ok ⟨targetAfter m i a hi ha t,List.prefix_refl _⟩ := by
  let first : State C Γ := t.setLocal (boolSlot m i hi) (TEnv.get (boolSlot m a ha) t.env)
  let finish : State C Γ := (first.setLocal (boolSlot m a ha) false).setLocal (boolSlot m i hi) false
  let step : Out C t.H Γ → TRes (Out C t.H Γ) := fun o =>
    ((body m i a hi ha : Prog C Γ Γ).run o.st).map fun o' =>
      ⟨o'.st.drop (body m i a hi ha : Prog C Γ Γ).ext,o.ext.trans o'.ext⟩
  let test : Out C t.H Γ → TRes Bool := fun o =>
    (Val.simple (.local (boolSlot m i hi)) : Val C Γ .bool).evalT o.st
  have htest : test ⟨first,List.prefix_refl _⟩ = .ok (TEnv.get (boolSlot m a ha) t.env) := by
    change Except.ok (TEnv.get (boolSlot m i hi)
      (TEnv.set (boolSlot m i hi) (TEnv.get (boolSlot m a ha) t.env) t.env)) = _
    rw [TEnv.get_set]
  have hstep : step ⟨first,List.prefix_refl _⟩ = .ok ⟨finish,List.prefix_refl _⟩ := by
    exact congrArg (fun result : TRes (Out C first.H Γ) => result.map
      (fun o' => (⟨o'.st.drop (body m i a hi ha : Prog C Γ Γ).ext,
        (List.prefix_refl t.H).trans o'.ext⟩ : Out C t.H Γ)))
      (body_run m i a hi ha first)
  have hstop : test ⟨finish,List.prefix_refl _⟩ = .ok false := by
    change Except.ok (TEnv.get (boolSlot m i hi)
      (TEnv.set (boolSlot m i hi) false (TEnv.set (boolSlot m a ha) false first.env))) = _
    rw [TEnv.get_set]
  have loopRun : TLoop.run step test ⟨first,List.prefix_refl _⟩ =
      .ok (⟨targetAfter m i a hi ha t,List.prefix_refl _⟩ : Out C t.H Γ) := by
    calc
      _ = .ok (if (TEnv.get (boolSlot m a ha) t.env : Bool) = true then
          ⟨finish,List.prefix_refl _⟩ else ⟨first,List.prefix_refl _⟩) :=
        run_reset_loop step test _ _ _ htest hstep hstop
      _ = _ := by
        cases choice : (TEnv.get (boolSlot m a ha) t.env : Bool)
        · simp only [targetAfter,first,State.setLocal,choice] <;> rfl
        · simp only [targetAfter,first,finish,choice] <;> rfl
  exact loopRun

theorem block_run {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) (t : State C Γ) :
    (Stmt.block (AssignmentWhileBreak.code m i a hi ha) : Stmt C Γ Γ).run t =
      .ok ⟨t.setLocal (boolSlot m i hi) (TEnv.get (boolSlot m a ha) t.env),List.prefix_refl _⟩ := by
  have prefixRun : (AssignmentWhileBreak.code m i a hi ha : Prog C Γ Γ).run t =
      .ok ⟨t.setLocal (boolSlot m i hi) (TEnv.get (boolSlot m a ha) t.env),List.prefix_refl _⟩ := AssignmentWhileBreak.target_run m i a hi ha t
  unfold Prog.run at prefixRun
  unfold Stmt.run
  change TRun.block (AssignmentWhileBreak.code m i a hi ha : Prog C Γ Γ).ext
    (AssignmentWhileBreak.code m i a hi ha : Prog C Γ Γ).runR t = _
  unfold TRun.block
  rw [prefixRun]
  rfl

theorem target_run {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) (t : State C Γ) :
    (code m i a hi ha : Prog C Γ Γ).run t =
      .ok ⟨targetAfter m i a hi ha t,List.prefix_refl _⟩  := by
  rw [code,Prog.run_cons_ok (block_run m i a hi ha t),
    Prog.run_cons_ok (loop_run m i a hi ha t),Prog.run_nil]
  rfl


theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
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
    (mapA : m.slot a = ⟨.val .bool,boolSlot m a ha⟩) :
    let choice : Bool := TEnv.get (boolSlot m a ha) t.env
    (Source.execS G F (fuel+4) nps ph (R := returns) (M := M)
      (.whileLoop (l := l) (u := u) (.assign (.local i) (.local a))
        (.expr (.assign (.local a) (.bool false)))) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (sourceAfter s.1 i a choice)),(.nil,s.2)) ∧
    (code m i a hi ha : Prog C Γ Γ).run t =
      .ok ⟨targetAfter m i a hi ha t,List.prefix_refl _⟩ ∧
    m.Related R (sourceAfter s.1 i a choice) (targetAfter m i a hi ha t).env ∧
    (targetAfter m i a hi ha t).glob = t.glob := by
  dsimp only
  have read : s.1.get a = .bool (TEnv.get (boolSlot m a ha) t.env) :=
    boolReflect _ _ (ContextMap.value_at m R s.1 t.env aligned a _ mapA)
  have first : m.Related R (s.1.set i (.bool (TEnv.get (boolSlot m a ha) t.env)))
      (TEnv.set (boolSlot m i hi) (TEnv.get (boolSlot m a ha) t.env) t.env) := by
    intro τ k
    rw [←read]
    exact ContextMap.related_assign m R s.1 t.env aligned i a
      (boolSlot m i hi) (boolSlot m a ha) mapI mapA k
  have reset : m.Related R ((s.1.set i (.bool (TEnv.get (boolSlot m a ha) t.env))).set a (.bool false))
      (TEnv.set (boolSlot m a ha) false
        (TEnv.set (boolSlot m i hi) (TEnv.get (boolSlot m a ha) t.env) t.env)) :=
    by
      intro τ k
      exact ContextMap.related_write m R _ _ first a (boolSlot m a ha) mapA (.bool false) false falseValue k
  have final : m.Related R
      (((s.1.set i (.bool (TEnv.get (boolSlot m a ha) t.env))).set a (.bool false)).set i (.bool false))
      (TEnv.set (boolSlot m i hi) false (TEnv.set (boolSlot m a ha) false
        (TEnv.set (boolSlot m i hi) (TEnv.get (boolSlot m a ha) t.env) t.env))) := by
    intro τ k
    have h : R τ (m.slot k).1
        ((((s.1.set i (.bool (TEnv.get (boolSlot m a ha) t.env))).set a (.bool false)).set i
          (((s.1.set i (.bool (TEnv.get (boolSlot m a ha) t.env))).set a (.bool false)).get a)).get k)
        (TEnv.get (m.slot k).2 (TEnv.set (boolSlot m i hi)
          (TEnv.get (boolSlot m a ha) (TEnv.set (boolSlot m a ha) false
            (TEnv.set (boolSlot m i hi) (TEnv.get (boolSlot m a ha) t.env) t.env)))
          (TEnv.set (boolSlot m a ha) false
            (TEnv.set (boolSlot m i hi) (TEnv.get (boolSlot m a ha) t.env) t.env)))) :=
      ContextMap.related_assign m R _ _ reset i a (boolSlot m i hi) (boolSlot m a ha) mapI mapA k
    simpa only [source_locals_get_set,TEnv.get_set] using h
  refine ⟨source_run G F fuel nps ph s.1 s.2 i a _ read,target_run m i a hi ha t,?_,rfl⟩
  intro τ k
  cases choice : (TEnv.get (boolSlot m a ha) t.env : Bool)
  · simpa only [sourceAfter,targetAfter,State.setLocal,choice,ite_true,ite_false] using first k
  · simpa only [sourceAfter,targetAfter,State.setLocal,choice,ite_true,ite_false] using final k

theorem source_zero {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M l u : Bool}
    (ls : Source.Locals E.layout srcΓ) (i a : Source.Idx srcΓ .bool) :
    Source.execS G F 0 nps ph (R := returns) (M := M)
      (.whileLoop (l := l) (u := u) (.assign (.local i) (.local a))
        (.expr (.assign (.local a) (.bool false)))) ls = Source.EM.halt .timeout := by rfl

end Solidity.Lowering.G19.AssignmentWhileReset
