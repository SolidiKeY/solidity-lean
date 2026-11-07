import Solidity.Lowering.G19.ReturnTail

/-! Extend the existing V07-related captured return selector by another real
assignment. Both suffixes read reached locals; the private selector is reused. -/
namespace Solidity.Lowering.G19.ReturnPair
open Solidity.Lowering.V07

def statement {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy} {M : Bool} {k : Source.SCtx}
    (ci ca : Source.Idx Γ .bool) (i a : Source.Idx Γ τ) (dest donor : Source.Idx Γ σ) :
    Source.RStmt E [] M k Γ Γ :=
  .block (.stmt (ReturnTail.statement ci ca i a)
    (.stmt (.expr (.assign (.local dest) (.local donor))) .nil))

def sourceAfter {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (s : Source.EMState E Γ) (ci : Source.Idx Γ .bool) (choice : Bool)
    (i a : Source.Idx Γ τ) (dest donor : Source.Idx Γ σ) : Source.EMState E Γ :=
  let first := ReturnTail.sourceAfter s ci choice i a
  (if choice then first.1 else first.1.set dest (first.1.get donor),s.2)

def code {C : Contract} {Γ : Ctx} {p q : PrimTy} (ci ca : Idx Γ (.val .bool))
    (i a : Idx Γ (.val p)) (dest donor : Idx Γ (.val q)) : Prog C Γ (.val .bool :: Γ) :=
  (ReturnTail.code ci ca i a).join (ReturnTail.suffix dest donor)

def callerAfter {C : Contract} {Γ : Ctx} {p q : PrimTy} (s : State C Γ)
    (ci : Idx Γ (.val .bool)) (choice : Bool) (i a : Idx Γ (.val p))
    (dest donor : Idx Γ (.val q)) : State C Γ :=
  let first := ReturnTail.callerAfter s ci choice i a
  first.withEnv (if choice then first.env else TEnv.set dest (TEnv.get donor first.env) first.env)

def reached {C : Contract} {Γ : Ctx} {p q : PrimTy} (s : State C Γ)
    (ci : Idx Γ (.val .bool)) (choice : Bool) (i a : Idx Γ (.val p))
    (dest donor : Idx Γ (.val q)) : State C (.val .bool :: Γ) :=
  (callerAfter s ci choice i a dest donor).push (t := .val .bool) choice

theorem source_run {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γ)
    (ci ca : Source.Idx Γ .bool) (choice : Bool) (i a : Source.Idx Γ τ)
    (dest donor : Source.Idx Γ σ) (read : s.1.get ca = .bool choice) :
    (Source.execS G F (fuel+8) nps ph (M := M) (statement (k := k) ci ca i a dest donor) s.1).run
      (.nil,s.2) =
      (.ok (if choice then Source.Out.ret (sourceAfter s ci choice i a dest donor).1
        else Source.Out.normal (sourceAfter s ci choice i a dest donor).1),(.nil,s.2)) := by
  have prefixRun : (Source.execS G F (fuel+6) nps ph (M := M)
      (ReturnTail.statement (k := k) ci ca i a) s.1).run (.nil,s.2) =
      (.ok (if choice then Source.Out.ret (ReturnTail.sourceAfter s ci choice i a).1
        else Source.Out.normal (ReturnTail.sourceAfter s ci choice i a).1),(.nil,s.2)) :=
    ReturnTail.source_run G F fuel nps ph s ci ca choice i a read
  have restRun : (Source.execItems G F (fuel+6) nps ph (R := []) (M := M) (k := k)
      (.stmt (.expr (.assign (.local dest) (.local donor))) .nil)
      (ReturnTail.sourceAfter s ci choice i a).1).run (.nil,s.2) =
      (.ok (Source.Out.normal ((ReturnTail.sourceAfter s ci choice i a).1.set dest
        ((ReturnTail.sourceAfter s ci choice i a).1.get donor))),(.nil,s.2)) :=
    ReturnTail.source_tail_items_run G F (fuel+2) nps ph
      (ReturnTail.sourceAfter s ci choice i a) dest donor
  rw [statement,Source.execS,Source.Hoare.run_bind]
  have itemsRun : (Source.execItems G F (fuel+7) nps ph (R := []) (M := M) (k := k)
      (.stmt (ReturnTail.statement ci ca i a)
        (.stmt (.expr (.assign (.local dest) (.local donor))) .nil)) s.1).run (.nil,s.2) =
      (.ok (if choice then Source.Out.ret (sourceAfter s ci choice i a dest donor).1
        else Source.Out.normal (sourceAfter s ci choice i a dest donor).1),(.nil,s.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,prefixRun]
    cases choice
    · simp only [Bool.false_eq_true,if_false]
      rw [Source.Hoare.run_bind,restRun]
      rfl
    · rfl
  rw [itemsRun]
  cases choice <;> simp only [sourceAfter,Source.Out.close,ReturnTail.source_locals_restore_self] <;> rfl

theorem target_run {C : Contract} {Γ : Ctx} {p q : PrimTy} (s : State C Γ)
    (ci ca : Idx Γ (.val .bool)) (choice : Bool) (i a : Idx Γ (.val p))
    (dest donor : Idx Γ (.val q)) (read : TEnv.get ca s.env = choice) :
    (code ci ca i a dest donor).run s =
      .ok ⟨reached s ci choice i a dest donor,List.prefix_refl _⟩ := by
  have prefixRun : (ReturnTail.code ci ca i a).run s =
      .ok ⟨ReturnTail.reached s ci choice i a,List.prefix_refl _⟩ :=
    ReturnTail.target_run s ci ca choice i a read
  have tailRun : (ReturnTail.suffix dest donor).run (ReturnTail.reached s ci choice i a) =
      .ok ⟨reached s ci choice i a dest donor,List.prefix_refl _⟩ := by
    cases choice <;> rfl
  unfold Prog.run at prefixRun tailRun
  rw [code,DeferredSource.join_run]
  unfold TRun.seq
  rw [prefixRun]
  dsimp only
  rw [tailRun]
  rfl

theorem correct {E : Source.Env} {Γs : Source.RCtx} {τ σ : Source.STy}
    {C : Contract} {Γ : Ctx} {p q : PrimTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γs) (t : State C Γ) (m : ContextMap Γs Γ)
    (R : (α : Source.STy) → (u : LTy) → Source.Val E.layout α → u.TDenote C t.H → Prop)
    (aligned : m.Related R s.1 t.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool), R .bool (.val .bool) v b → v = .bool b)
    (ci ca : Source.Idx Γs .bool) (i a : Source.Idx Γs τ) (dest donor : Source.Idx Γs σ)
    (tci tca : Idx Γ (.val .bool)) (ti ta : Idx Γ (.val p)) (tdest tdonor : Idx Γ (.val q))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapI : m.slot i = ⟨.val p,ti⟩) (mapA : m.slot a = ⟨.val p,ta⟩)
    (mapDest : m.slot dest = ⟨.val q,tdest⟩) (mapDonor : m.slot donor = ⟨.val q,tdonor⟩) :
    let choice : Bool := TEnv.get tca t.env
    (Source.execS G F (fuel+8) nps ph (M := M) (statement (k := k) ci ca i a dest donor) s.1).run
      (.nil,s.2) =
      (.ok (if choice then Source.Out.ret (sourceAfter s ci choice i a dest donor).1
        else Source.Out.normal (sourceAfter s ci choice i a dest donor).1),(.nil,s.2)) ∧
    (code tci tca ti ta tdest tdonor).run t =
      .ok ⟨reached t tci choice ti ta tdest tdonor,List.prefix_refl _⟩ ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R
      (sourceAfter s ci choice i a dest donor).1 (reached t tci choice ti ta tdest tdonor).env ∧
    TEnv.get .here (reached t tci choice ti ta tdest tdonor).env = choice ∧
    (reached t tci choice ti ta tdest tdonor).glob = t.glob := by
  dsimp only
  have read : s.1.get ca = .bool (TEnv.get tca t.env) :=
    boolReflect _ _ (ContextMap.value_at m R s.1 t.env aligned ca tca mapCA)
  rcases ReturnTail.correct G F fuel nps ph (M := M) (k := k) s t m R aligned boolReflect
    ci ca i a tci tca ti ta mapCI mapCA mapI mapA with ⟨_,_,related,_,_⟩
  have first : m.Related R (ReturnTail.sourceAfter s ci (TEnv.get tca t.env) i a).1
      (ReturnTail.callerAfter t tci (TEnv.get tca t.env) ti ta).env := by
    intro α j
    exact related j
  have tailRelated : m.Related R
      ((ReturnTail.sourceAfter s ci (TEnv.get tca t.env) i a).1.set dest
        ((ReturnTail.sourceAfter s ci (TEnv.get tca t.env) i a).1.get donor))
      (TEnv.set tdest (TEnv.get tdonor (ReturnTail.callerAfter t tci (TEnv.get tca t.env) ti ta).env)
        (ReturnTail.callerAfter t tci (TEnv.get tca t.env) ti ta).env) :=
    ContextMap.related_assign m R _ _ first dest donor tdest tdonor mapDest mapDonor
  have post : (m.wk (Thin.drop (t := .val .bool) .refl)).Related R
      (sourceAfter s ci (TEnv.get tca t.env) i a dest donor).1
      (reached t tci (TEnv.get tca t.env) ti ta tdest tdonor).env := by
    cases choice : TEnv.get tca t.env
    · rw [choice] at tailRelated
      intro α j
      exact tailRelated j
    · rw [choice] at first
      intro α j
      exact first j
  exact ⟨source_run G F fuel nps ph s ci ca _ i a dest donor read,
    target_run t tci tca _ ti ta tdest tdonor rfl,post,rfl,rfl⟩

theorem source_zero {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γ)
    (ci ca : Source.Idx Γ .bool) (i a : Source.Idx Γ τ) (dest donor : Source.Idx Γ σ) :
    Source.execS G F 0 nps ph (M := M) (statement (k := k) ci ca i a dest donor) s.1 =
      Source.EM.halt .timeout := by rfl

end Solidity.Lowering.G19.ReturnPair
