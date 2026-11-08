import Solidity.Lowering.V07.ConditionalAssignments
import Solidity.Lowering.G19.AssignmentReturnFlag

/-! Statement-level consumer of the published V07 conditional assignment
producer. Existing intrinsic source statements and target blocks only. -/
namespace Solidity.Lowering.G19.ConditionalStatement
open Solidity.Lowering.V07

def statement {E : Source.Env} {srcΓ : Source.RCtx} {τ : Source.STy}
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (ci ca : Source.Idx srcΓ .bool) (i a j b : Source.Idx srcΓ τ) :
    Source.RStmt E R M k srcΓ srcΓ :=
  .ifElse (.assign (.local ci) (.local ca))
    (.expr (.assign (.local i) (.local a))) (.expr (.assign (.local j) (.local b)))

def code {C : Contract} {Γ : Ctx} {p : PrimTy} (ci ca : Idx Γ (.val .bool))
    (i a j b : Idx Γ (.val p)) : Prog C Γ Γ :=
  .cons (.block (ConditionalAssignments.code ci ca i a j b)) .nil

/-- Actual if/else statement execution, including the caller condition write. -/
theorem source_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (s : Source.EMState E Γ) (ci ca : Source.Idx Γ .bool) (choice : Bool)
    (i a j b : Source.Idx Γ τ) (read : s.1.get ca = .bool choice) :
    (Source.execS G F (fuel+4) nps ph (R := R) (M := M)
      (statement (k := k) ci ca i a j b) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (ConditionalAssignments.sourceAfter s ci choice i a j b).1),(.nil,s.2)) := by
  have sub : (Source.EM.sub s.1 (Source.evalE G F (fuel+3)
      (.assign (.local ci) (.local ca)))).run (.nil,s.2) =
      (.ok (.val (.bool choice),s.1.set ci (.bool choice)),(.nil,s.2)) :=
    AssignmentReturnFlag.assignment_sub_run G F (fuel+1) s.1 s.2 ci ca (.bool choice) read
  have branchRun (dest donor : Source.Idx Γ τ) :
      (Source.execS G F (fuel+3) nps ph (R := R) (M := M) (k := k)
        (.expr (.assign (.local dest) (.local donor))) (s.1.set ci (.bool choice))).run (.nil,s.2) =
      (.ok (Source.Out.normal ((s.1.set ci (.bool choice)).set dest
        ((s.1.set ci (.bool choice)).get donor))),(.nil,s.2)) := by
    have h : (Source.evalE G F (fuel+2) (.assign (.local dest) (.local donor))).run
        (s.1.set ci (.bool choice),s.2) =
        (.ok (.val ((s.1.set ci (.bool choice)).get donor)),
          ((s.1.set ci (.bool choice)).set dest ((s.1.set ci (.bool choice)).get donor),s.2)) :=
      source_assign_local_run G F fuel (s.1.set ci (.bool choice),s.2) dest donor _ rfl
    simp only [ExceptT.run] at h
    have hsub : (Source.EM.sub (s.1.set ci (.bool choice)) (Source.evalE G F (fuel+2)
        (.assign (.local dest) (.local donor)))).run (.nil,s.2) =
        (.ok (.val ((s.1.set ci (.bool choice)).get donor),
          (s.1.set ci (.bool choice)).set dest ((s.1.set ci (.bool choice)).get donor)),(.nil,s.2)) := by
      simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,h]
    rw [Source.execS,Source.Hoare.run_bind,hsub]
    rfl
  have restore (ls : Source.Locals E.layout Γ) : ls.restore Γ = .ok ls := by
    unfold Source.Locals.restore
    generalize count : Γ.length - Γ.length = n
    have zero : n = 0 := by omega
    cases zero
    simp only [List.drop_zero, ↓reduceDIte, Source.Locals.drop]
    rfl
  rw [statement,Source.execS,Source.Hoare.run_bind,sub]
  dsimp only
  rw [Source.Hoare.run_bind,source_getV_run]
  cases choice
  · dsimp only
    rw [Source.Hoare.run_bind,branchRun j b]
    simp only [Source.Out.close,restore]
    rfl
  · dsimp only
    rw [Source.Hoare.run_bind,branchRun i a]
    simp only [Source.Out.close,restore]
    rfl

theorem target_run {C : Contract} {Γ : Ctx} {p : PrimTy}
    (s : State C Γ) (ci ca : Idx Γ (.val .bool)) (choice : Bool)
    (i a j b : Idx Γ (.val p)) (read : TEnv.get ca s.env = choice) :
    (code ci ca i a j b).run s =
      .ok ⟨ConditionalAssignments.targetAfter s ci choice i a j b,List.prefix_refl _⟩ := by
  have prefixRun : (ConditionalAssignments.code ci ca i a j b).run s =
      .ok ⟨((ConditionalAssignments.targetAfter s ci choice i a j b).push (t := .val .bool) choice).push
        (TEnv.get (if choice then a else b) (TEnv.set ci choice s.env)),List.prefix_refl _⟩ :=
    ConditionalAssignments.prefix_run s ci ca choice i a j b read
  unfold Prog.run at prefixRun
  have blockRun : (Stmt.block (ConditionalAssignments.code ci ca i a j b) : Stmt C Γ Γ).run s =
      .ok ⟨ConditionalAssignments.targetAfter s ci choice i a j b,List.prefix_refl _⟩ := by
    show TRun.block (ConditionalAssignments.code ci ca i a j b).ext
      (ConditionalAssignments.code ci ca i a j b).runR s = _
    unfold TRun.block
    rw [prefixRun]
    rfl
  rw [code,Prog.run_cons_ok blockRun,Prog.run_nil]
  rfl

theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {τ : Source.STy}
    {C : Contract} {Γ : Ctx} {p : PrimTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M : Bool} {k : Source.SCtx}
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (σ : Source.STy) → (u : LTy) → Source.Val E.layout σ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (c : Bool), R .bool (.val .bool) v c → v = .bool c)
    (ci ca : Source.Idx srcΓ .bool) (i a j b : Source.Idx srcΓ τ)
    (tci tca : Idx Γ (.val .bool)) (ti ta tj tb : Idx Γ (.val p))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapI : m.slot i = ⟨.val p,ti⟩) (mapA : m.slot a = ⟨.val p,ta⟩)
    (mapJ : m.slot j = ⟨.val p,tj⟩) (mapB : m.slot b = ⟨.val p,tb⟩) :
    let choice : Bool := TEnv.get tca target.env
    (Source.execS G F (fuel+4) nps ph (R := returns) (M := M)
      (statement (k := k) ci ca i a j b) source.1).run (.nil,source.2) =
      (.ok (Source.Out.normal (ConditionalAssignments.sourceAfter source ci choice i a j b).1),(.nil,source.2)) ∧
    (code tci tca ti ta tj tb).run target =
      .ok ⟨ConditionalAssignments.targetAfter target tci choice ti ta tj tb,List.prefix_refl _⟩ ∧
    m.Related R (ConditionalAssignments.sourceAfter source ci choice i a j b).1
      (ConditionalAssignments.targetAfter target tci choice ti ta tj tb).env ∧
    (ConditionalAssignments.targetAfter target tci choice ti ta tj tb).glob = target.glob := by
  dsimp only
  have read : source.1.get ca = .bool (TEnv.get tca target.env) :=
    boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned ca tca mapCA)
  rcases ConditionalAssignments.transport G F fuel source target m R aligned boolReflect
    ci ca i a j b tci tca ti ta tj tb mapCI mapCA mapI mapA mapJ mapB with ⟨_,_,_,related⟩
  exact ⟨source_run G F fuel nps ph source ci ca _ i a j b read,
    target_run target tci tca _ ti ta tj tb rfl,related,rfl⟩

theorem source_zero {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (s : Source.EMState E Γ) (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) :
    Source.execS G F 0 nps ph (R := R) (M := M) (statement (k := k) ci ca i a j b) s.1 =
      Source.EM.halt .timeout := by rfl

end Solidity.Lowering.G19.ConditionalStatement
