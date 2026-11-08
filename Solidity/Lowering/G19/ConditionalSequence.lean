import Solidity.Lowering.G19.ConditionalStatement

/-! Actual conditional statement followed by an assignment in its caller
context. Uses V07 ContextMap and the already scoped conditional producer. -/
namespace Solidity.Lowering.G19.ConditionalSequence
open Solidity.Lowering.V07

def statement {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) (dest donor : Source.Idx Γ σ) :
    Source.RStmt E R M k Γ Γ :=
  .block (.stmt (ConditionalStatement.statement ci ca i a j b)
    (.stmt (.expr (.assign (.local dest) (.local donor))) .nil))

def sourceAfter {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (s : Source.EMState E Γ) (ci : Source.Idx Γ .bool) (choice : Bool)
    (i a j b : Source.Idx Γ τ) (dest donor : Source.Idx Γ σ) : Source.EMState E Γ :=
  let post := ConditionalAssignments.sourceAfter s ci choice i a j b
  (post.1.set dest (post.1.get donor),post.2)

def code {C : Contract} {Γ : Ctx} {p q : PrimTy} (ci ca : Idx Γ (.val .bool))
    (i a j b : Idx Γ (.val p)) (dest donor : Idx Γ (.val q)) : Prog C Γ Γ :=
  .cons (.block (ConditionalStatement.code ci ca i a j b))
    (.cons (.assignLocal dest (.simple (.local donor))) .nil)

def targetAfter {C : Contract} {Γ : Ctx} {p q : PrimTy}
    (s : State C Γ) (ci : Idx Γ (.val .bool)) (choice : Bool)
    (i a j b : Idx Γ (.val p)) (dest donor : Idx Γ (.val q)) : State C Γ :=
  let post := ConditionalAssignments.targetAfter s ci choice i a j b
  post.setLocal dest (TEnv.get donor post.env)

theorem source_run {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (s : Source.EMState E Γ) (ci ca : Source.Idx Γ .bool) (choice : Bool)
    (i a j b : Source.Idx Γ τ) (dest donor : Source.Idx Γ σ) (read : s.1.get ca = .bool choice) :
    (Source.execS G F (fuel+6) nps ph (R := R) (M := M)
      (statement (k := k) ci ca i a j b dest donor) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (sourceAfter s ci choice i a j b dest donor).1),(.nil,s.2)) := by
  have prefixRun : (Source.execS G F (fuel+4) nps ph (R := R) (M := M)
      (ConditionalStatement.statement (k := k) ci ca i a j b) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (ConditionalAssignments.sourceAfter s ci choice i a j b).1),(.nil,s.2)) :=
    ConditionalStatement.source_run G F fuel nps ph s ci ca choice i a j b read
  have hr : Source.evalE (plan := none) (calldataKnown := true) G F (fuel+2) (.assign (.local dest) (.local donor))
      ((ConditionalAssignments.sourceAfter s ci choice i a j b).1,s.2) =
      (.ok (.val ((ConditionalAssignments.sourceAfter s ci choice i a j b).1.get donor)),
        sourceAfter s ci choice i a j b dest donor) :=
    source_assign_local_run G F fuel (ConditionalAssignments.sourceAfter s ci choice i a j b) dest donor _ rfl
  have sub : (Source.EM.sub (ConditionalAssignments.sourceAfter s ci choice i a j b).1
      (Source.evalE G F (fuel+2) (.assign (.local dest) (.local donor)))).run (.nil,s.2) =
      (.ok (.val ((ConditionalAssignments.sourceAfter s ci choice i a j b).1.get donor),
        (sourceAfter s ci choice i a j b dest donor).1),(.nil,s.2)) := by
    simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,hr]
    rfl
  have tailRun : (Source.execS G F (fuel+3) nps ph (R := R) (M := M) (k := k)
      (.expr (.assign (.local dest) (.local donor)))
      (ConditionalAssignments.sourceAfter s ci choice i a j b).1).run (.nil,s.2) =
      (.ok (Source.Out.normal (sourceAfter s ci choice i a j b dest donor).1),(.nil,s.2)) := by
    rw [Source.execS,Source.Hoare.run_bind,sub]
    rfl
  have restRun : (Source.execItems G F (fuel+4) nps ph (R := R) (M := M) (k := k)
      (.stmt (.expr (.assign (.local dest) (.local donor))) .nil)
      (ConditionalAssignments.sourceAfter s ci choice i a j b).1).run (.nil,s.2) =
      (.ok (Source.Out.normal (sourceAfter s ci choice i a j b dest donor).1),(.nil,s.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,tailRun]
    rfl
  have itemsRun : (Source.execItems G F (fuel+5) nps ph (R := R) (M := M) (k := k)
      (.stmt (ConditionalStatement.statement ci ca i a j b)
        (.stmt (.expr (.assign (.local dest) (.local donor))) .nil)) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (sourceAfter s ci choice i a j b dest donor).1),(.nil,s.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,prefixRun]
    dsimp only
    rw [Source.Hoare.run_bind,restRun]
    rfl
  have restore (ls : Source.Locals E.layout Γ) : ls.restore Γ = .ok ls := by
    unfold Source.Locals.restore
    generalize count : Γ.length - Γ.length = n
    have zero : n = 0 := by omega
    cases zero
    simp only [List.drop_zero, ↓reduceDIte, Source.Locals.drop]
    rfl
  rw [statement,Source.execS,Source.Hoare.run_bind,itemsRun]
  simp only [Source.Out.close,restore]
  rfl

theorem target_run {C : Contract} {Γ : Ctx} {p q : PrimTy}
    (s : State C Γ) (ci ca : Idx Γ (.val .bool)) (choice : Bool)
    (i a j b : Idx Γ (.val p)) (dest donor : Idx Γ (.val q)) (read : TEnv.get ca s.env = choice) :
    (code ci ca i a j b dest donor).run s =
      .ok ⟨targetAfter s ci choice i a j b dest donor,List.prefix_refl _⟩ := by
  have prefixRun : (ConditionalStatement.code ci ca i a j b).run s =
      .ok ⟨ConditionalAssignments.targetAfter s ci choice i a j b,List.prefix_refl _⟩ :=
    ConditionalStatement.target_run s ci ca choice i a j b read
  unfold Prog.run at prefixRun
  have blockRun : (Stmt.block (ConditionalStatement.code ci ca i a j b) : Stmt C Γ Γ).run s =
      .ok ⟨ConditionalAssignments.targetAfter s ci choice i a j b,List.prefix_refl _⟩ := by
    show TRun.block (ConditionalStatement.code ci ca i a j b).ext
      (ConditionalStatement.code ci ca i a j b).runR s = _
    unfold TRun.block
    rw [prefixRun]
    rfl
  have tailRun : (Stmt.assignLocal dest (.simple (.local donor))).run
      (ConditionalAssignments.targetAfter s ci choice i a j b) =
      .ok ⟨targetAfter s ci choice i a j b dest donor,List.prefix_refl _⟩ := rfl
  rw [code,Prog.run_cons_ok blockRun,Prog.run_cons_ok tailRun,Prog.run_nil]
  rfl

theorem correct {E : Source.Env} {Γs : Source.RCtx} {τ σ : Source.STy}
    {C : Contract} {Γ : Ctx} {p q : PrimTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M : Bool} {k : Source.SCtx}
    (s : Source.EMState E Γs) (t : State C Γ) (m : ContextMap Γs Γ)
    (R : (α : Source.STy) → (u : LTy) → Source.Val E.layout α → u.TDenote C t.H → Prop)
    (aligned : m.Related R s.1 t.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool), R .bool (.val .bool) v b → v = .bool b)
    (ci ca : Source.Idx Γs .bool) (i a j b : Source.Idx Γs τ) (dest donor : Source.Idx Γs σ)
    (tci tca : Idx Γ (.val .bool)) (ti ta tj tb : Idx Γ (.val p)) (tdest tdonor : Idx Γ (.val q))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapI : m.slot i = ⟨.val p,ti⟩) (mapA : m.slot a = ⟨.val p,ta⟩)
    (mapJ : m.slot j = ⟨.val p,tj⟩) (mapB : m.slot b = ⟨.val p,tb⟩)
    (mapDest : m.slot dest = ⟨.val q,tdest⟩) (mapDonor : m.slot donor = ⟨.val q,tdonor⟩) :
    let choice : Bool := TEnv.get tca t.env
    (Source.execS G F (fuel+6) nps ph (R := returns) (M := M)
      (statement (k := k) ci ca i a j b dest donor) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (sourceAfter s ci choice i a j b dest donor).1),(.nil,s.2)) ∧
    (code tci tca ti ta tj tb tdest tdonor).run t =
      .ok ⟨targetAfter t tci choice ti ta tj tb tdest tdonor,List.prefix_refl _⟩ ∧
    m.Related R (sourceAfter s ci choice i a j b dest donor).1
      (targetAfter t tci choice ti ta tj tb tdest tdonor).env ∧
    (targetAfter t tci choice ti ta tj tb tdest tdonor).glob = t.glob := by
  dsimp only
  have read : s.1.get ca = .bool (TEnv.get tca t.env) :=
    boolReflect _ _ (ContextMap.value_at m R s.1 t.env aligned ca tca mapCA)
  rcases ConditionalStatement.correct G F fuel nps ph (returns := returns) (M := M) (k := k)
    s t m R aligned boolReflect ci ca i a j b tci tca ti ta tj tb mapCI mapCA mapI mapA mapJ mapB
    with ⟨_,_,prefixRelated,_⟩
  have post : m.Related R (sourceAfter s ci (TEnv.get tca t.env) i a j b dest donor).1
      (targetAfter t tci (TEnv.get tca t.env) ti ta tj tb tdest tdonor).env :=
    ContextMap.related_assign m R _ _ prefixRelated dest donor tdest tdonor mapDest mapDonor
  exact ⟨source_run G F fuel nps ph s ci ca _ i a j b dest donor read,
    target_run t tci tca _ ti ta tj tb tdest tdonor rfl,post,rfl⟩

theorem source_zero {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (s : Source.EMState E Γ) (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ)
    (dest donor : Source.Idx Γ σ) :
    Source.execS G F 0 nps ph (R := R) (M := M)
      (statement (k := k) ci ca i a j b dest donor) s.1 = Source.EM.halt .timeout := by rfl

end Solidity.Lowering.G19.ConditionalSequence
