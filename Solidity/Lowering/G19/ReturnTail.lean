import Solidity.Lowering.G19.AssignmentReturnFlag

/-! Consume the existing mapped return selector to suppress a real caller
assignment. The fresh Boolean represents Source's bare-return outcome;
function-exit bytecode and arbitrary continuations remain separate. -/
namespace Solidity.Lowering.G19.ReturnTail
open Solidity.Lowering.V07

def statement {E : Source.Env} {Γ : Source.RCtx} {σ : Source.STy} {M : Bool} {k : Source.SCtx}
    (ci ca : Source.Idx Γ .bool) (dest donor : Source.Idx Γ σ) : Source.RStmt E [] M k Γ Γ :=
  .block (.stmt (.ifThen (.assign (.local ci) (.local ca)) (.ret rfl))
    (.stmt (.expr (.assign (.local dest) (.local donor))) .nil))

def sourceAfter {E : Source.Env} {Γ : Source.RCtx} {σ : Source.STy}
    (s : Source.EMState E Γ) (ci : Source.Idx Γ .bool) (choice : Bool)
    (dest donor : Source.Idx Γ σ) : Source.EMState E Γ :=
  let first := s.1.set ci (.bool choice)
  (if choice then first else first.set dest (first.get donor),s.2)

def suffix {C : Contract} {Γ : Ctx} {p : PrimTy} (dest donor : Idx Γ (.val p)) :
    Prog C (.val .bool :: Γ) (.val .bool :: Γ) :=
  .cons (.ite (.simple (.local .here)) .nil
    (.cons (.assignLocal (.there dest) (.simple (.local (.there donor)))) .nil)) .nil

def code {C : Contract} {Γ : Ctx} {p : PrimTy} (ci ca : Idx Γ (.val .bool))
    (dest donor : Idx Γ (.val p)) : Prog C Γ (.val .bool :: Γ) :=
  (assignLocalOperand ci ca).code.join (suffix dest donor)

def callerAfter {C : Contract} {Γ : Ctx} {p : PrimTy}
    (s : State C Γ) (ci : Idx Γ (.val .bool)) (choice : Bool) (dest donor : Idx Γ (.val p)) : State C Γ :=
  let first := s.setLocal ci choice
  first.withEnv (if choice then first.env else TEnv.set dest (TEnv.get donor first.env) first.env)

def reached {C : Contract} {Γ : Ctx} {p : PrimTy}
    (s : State C Γ) (ci : Idx Γ (.val .bool)) (choice : Bool) (dest donor : Idx Γ (.val p)) :
    State C (.val .bool :: Γ) :=
  (callerAfter s ci choice dest donor).push (t := .val .bool) choice

theorem source_locals_restore_self {E : Source.Env} {Γ : Source.RCtx}
  (ls : Source.Locals E.layout Γ) : ls.restore Γ = .ok ls := by
  unfold Source.Locals.restore
  generalize count : Γ.length - Γ.length = n
  have zero : n = 0 := by omega
  cases zero
  simp only [List.drop_zero, ↓reduceDIte, Source.Locals.drop]
  rfl

theorem source_tail_items_run {E : Source.Env} {Γ : Source.RCtx} {σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γ)
    (dest donor : Source.Idx Γ σ) :
    (Source.execItems G F (fuel+4) nps ph (R := []) (M := M) (k := k)
      (.stmt (.expr (.assign (.local dest) (.local donor))) .nil)
      s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (s.1.set dest
        (s.1.get donor))),(.nil,s.2)) := by
  have hr : Source.evalE G F (fuel+2) (.assign (.local dest) (.local donor)) (plan := none) (calldataKnown := true)
      s =
      (.ok (.val (s.1.get donor)),
        (s.1.set dest (s.1.get donor),s.2)) :=
    source_assign_local_run G F fuel s dest donor _ rfl
  have sub : (Source.EM.sub s.1
      (Source.evalE G F (fuel+2) (.assign (.local dest) (.local donor)))).run (.nil,s.2) =
      (.ok (.val (s.1.get donor),
        s.1.set dest (s.1.get donor)),(.nil,s.2)) := by
    simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,hr]
  have tailRun : (Source.execS G F (fuel+3) nps ph (R := []) (M := M) (k := k)
      (.expr (.assign (.local dest) (.local donor))) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (s.1.set dest
        (s.1.get donor))),(.nil,s.2)) := by
    rw [Source.execS,Source.Hoare.run_bind,sub]
    rfl
  have restRun : (Source.execItems G F (fuel+4) nps ph (R := []) (M := M) (k := k)
      (.stmt (.expr (.assign (.local dest) (.local donor))) .nil)
      s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (s.1.set dest
        (s.1.get donor))),(.nil,s.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,tailRun]
    rfl
  exact restRun

theorem source_run {E : Source.Env} {Γ : Source.RCtx} {σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γ)
    (ci ca : Source.Idx Γ .bool) (choice : Bool) (dest donor : Source.Idx Γ σ)
    (read : s.1.get ca = .bool choice) :
    (Source.execS G F (fuel+6) nps ph (R := []) (M := M)
      (statement (k := k) ci ca dest donor) s.1).run (.nil,s.2) =
      (.ok (if choice then Source.Out.ret (sourceAfter s ci choice dest donor).1
        else Source.Out.normal (sourceAfter s ci choice dest donor).1),(.nil,s.2)) := by
  have prefixRun : (Source.execS G F (fuel+4) nps ph (R := []) (M := M) (k := k)
      (.ifThen (.assign (.local ci) (.local ca)) (.ret rfl)) s.1).run (.nil,s.2) =
      (.ok (if choice then Source.Out.ret (s.1.set ci (.bool choice))
        else Source.Out.normal (s.1.set ci (.bool choice))),(.nil,s.2)) :=
    AssignmentReturnFlag.source_run G F (fuel+1) nps ph s.1 s.2 ci ca choice read
  have restRun : (Source.execItems G F (fuel+4) nps ph (R := []) (M := M) (k := k)
      (.stmt (.expr (.assign (.local dest) (.local donor))) .nil)
      (s.1.set ci (.bool choice))).run (.nil,s.2) =
      (.ok (Source.Out.normal ((s.1.set ci (.bool choice)).set dest
        ((s.1.set ci (.bool choice)).get donor))),(.nil,s.2)) := source_tail_items_run G F fuel nps ph (M := M) (k := k)
    (s.1.set ci (.bool choice),s.2) dest donor
  rw [statement,Source.execS,Source.Hoare.run_bind]
  have itemsRun : (Source.execItems G F (fuel+5) nps ph (R := []) (M := M) (k := k)
      (.stmt (.ifThen (.assign (.local ci) (.local ca)) (.ret rfl))
        (.stmt (.expr (.assign (.local dest) (.local donor))) .nil)) s.1).run (.nil,s.2) =
      (.ok (if choice then Source.Out.ret (sourceAfter s ci choice dest donor).1
        else Source.Out.normal (sourceAfter s ci choice dest donor).1),(.nil,s.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,prefixRun]
    cases choice
    · simp only [Bool.false_eq_true,if_false]
      rw [Source.Hoare.run_bind,restRun]
      rfl
    · rfl
  rw [itemsRun]
  cases choice <;> simp only [sourceAfter,Source.Out.close,source_locals_restore_self] <;> rfl

theorem suffix_run {C : Contract} {Γ : Ctx} {p : PrimTy}
    (s : State C Γ) (ci : Idx Γ (.val .bool)) (choice : Bool) (dest donor : Idx Γ (.val p)) :
    (suffix dest donor).run ((s.setLocal ci choice).push (t := .val .bool) choice) =
      .ok ⟨reached s ci choice dest donor,List.prefix_refl _⟩ := by
  cases choice <;> rfl

theorem target_run {C : Contract} {Γ : Ctx} {p : PrimTy}
    (s : State C Γ) (ci ca : Idx Γ (.val .bool)) (choice : Bool)
    (dest donor : Idx Γ (.val p)) (read : TEnv.get ca s.env = choice) :
    (code ci ca dest donor).run s = .ok ⟨reached s ci choice dest donor,List.prefix_refl _⟩ := by
  have prefixRun : (assignLocalOperand ci ca).code.run s =
      .ok ⟨(s.setLocal ci choice).push (t := .val .bool) choice,List.prefix_refl _⟩ := by
    rw [assigned_condition_prefix_run,read]
  have tailRun : (suffix dest donor).run ((s.setLocal ci choice).push (t := .val .bool) choice) =
      .ok ⟨reached s ci choice dest donor,List.prefix_refl _⟩ := suffix_run s ci choice dest donor
  unfold Prog.run at prefixRun tailRun
  rw [code,DeferredSource.join_run]
  unfold TRun.seq
  rw [prefixRun]
  dsimp only
  rw [tailRun]
  rfl

theorem correct {E : Source.Env} {Γs : Source.RCtx} {σ : Source.STy}
    {C : Contract} {Γ : Ctx} {p : PrimTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γs) (t : State C Γ) (m : ContextMap Γs Γ)
    (R : (α : Source.STy) → (u : LTy) → Source.Val E.layout α → u.TDenote C t.H → Prop)
    (aligned : m.Related R s.1 t.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool), R .bool (.val .bool) v b → v = .bool b)
    (ci ca : Source.Idx Γs .bool) (dest donor : Source.Idx Γs σ)
    (tci tca : Idx Γ (.val .bool)) (tdest tdonor : Idx Γ (.val p))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapDest : m.slot dest = ⟨.val p,tdest⟩) (mapDonor : m.slot donor = ⟨.val p,tdonor⟩) :
    let choice : Bool := TEnv.get tca t.env
    (Source.execS G F (fuel+6) nps ph (R := []) (M := M) (statement (k := k) ci ca dest donor) s.1).run (.nil,s.2) =
      (.ok (if choice then Source.Out.ret (sourceAfter s ci choice dest donor).1
        else Source.Out.normal (sourceAfter s ci choice dest donor).1),(.nil,s.2)) ∧
    (code tci tca tdest tdonor).run t = .ok ⟨reached t tci choice tdest tdonor,List.prefix_refl _⟩ ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R (sourceAfter s ci choice dest donor).1
      (reached t tci choice tdest tdonor).env ∧
    TEnv.get .here (reached t tci choice tdest tdonor).env = choice ∧
    (reached t tci choice tdest tdonor).glob = t.glob := by
  dsimp only
  have read : s.1.get ca = .bool (TEnv.get tca t.env) :=
    boolReflect _ _ (ContextMap.value_at m R s.1 t.env aligned ca tca mapCA)
  have postCaller (c : Bool) (sread : s.1.get ca = .bool c) (tread : TEnv.get tca t.env = c) :
      m.Related R (sourceAfter s ci c dest donor).1 (callerAfter t tci c tdest tdonor).env := by
    have first : m.Related R (s.1.set ci (.bool c)) (TEnv.set tci c t.env) := by
      have h : m.Related R (s.1.set ci (s.1.get ca)) (TEnv.set tci (TEnv.get tca t.env) t.env) :=
        ContextMap.related_assign m R s.1 t.env aligned ci ca tci tca mapCI mapCA
      rw [sread,tread] at h
      intro α i
      exact h i
    have fall : m.Related R ((s.1.set ci (.bool c)).set dest ((s.1.set ci (.bool c)).get donor))
        (TEnv.set tdest (TEnv.get tdonor (TEnv.set tci c t.env)) (TEnv.set tci c t.env)) :=
      ContextMap.related_assign m R _ _ first dest donor tdest tdonor mapDest mapDonor
    cases c
    · intro α i
      exact fall i
    · intro α i
      exact first i
  have post : (m.wk (Thin.drop (t := .val .bool) .refl)).Related R
      (sourceAfter s ci (TEnv.get tca t.env) dest donor).1
      (reached t tci (TEnv.get tca t.env) tdest tdonor).env := by
    intro α i
    exact (postCaller _ read rfl) i
  exact ⟨source_run G F fuel nps ph s ci ca _ dest donor read,
    target_run t tci tca _ tdest tdonor rfl,post,rfl,rfl⟩

theorem source_zero {E : Source.Env} {Γ : Source.RCtx} {σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γ)
    (ci ca : Source.Idx Γ .bool) (dest donor : Source.Idx Γ σ) :
    Source.execS G F 0 nps ph (R := []) (M := M) (statement (k := k) ci ca dest donor) s.1 = Source.EM.halt .timeout := by rfl

end Solidity.Lowering.G19.ReturnTail
