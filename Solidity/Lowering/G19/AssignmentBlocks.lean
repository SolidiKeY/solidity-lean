import Solidity.Lowering.G19.ReturnTail

/-! Finite ordered Boolean-write blocks, using V07 context-map transport.
List length is syntax size, not a source-loop unrolling restriction. -/
namespace Solidity.Lowering.G19.AssignmentBlocks
open Solidity.Lowering.V07

def sourceItems {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M : Bool} {k : Source.SCtx} :
    List (Source.Idx Γ .bool × Source.Idx Γ .bool) → Source.RItems E R M k Γ Γ
  | [] => .nil
  | (dest,donor) :: rest => .stmt (.expr (.assign (.local dest) (.local donor))) (sourceItems rest)

def statement {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (steps : List (Source.Idx Γ .bool × Source.Idx Γ .bool)) : Source.RStmt E R M k Γ Γ :=
  .block (sourceItems steps)

def sourceAfter {D : Source.Layout} {Γ : Source.RCtx} :
    List (Source.Idx Γ .bool × Source.Idx Γ .bool) → Source.Locals D Γ → Source.Locals D Γ
  | [],locals => locals
  | (dest,donor) :: rest,locals => sourceAfter rest (locals.set dest (locals.get donor))

def targetEnvAfter {srcΓ : Source.RCtx} {C : Contract} {H : HTy} {Γ : Ctx}
    (index : Source.Idx srcΓ .bool → Idx Γ (.val .bool)) :
    List (Source.Idx srcΓ .bool × Source.Idx srcΓ .bool) → TEnv C H Γ → TEnv C H Γ
  | [],env => env
  | (dest,donor) :: rest,env => targetEnvAfter index rest (TEnv.set (index dest) (TEnv.get (index donor) env) env)

def targetAfter {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (index : Source.Idx srcΓ .bool → Idx Γ (.val .bool))
    (steps : List (Source.Idx srcΓ .bool × Source.Idx srcΓ .bool)) (target : State C Γ) : State C Γ :=
  target.withEnv (targetEnvAfter index steps target.env)

def code {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (index : Source.Idx srcΓ .bool → Idx Γ (.val .bool)) :
    List (Source.Idx srcΓ .bool × Source.Idx srcΓ .bool) → Prog C Γ Γ
  | [] => .nil
  | (dest,donor) :: rest => .cons (.assignLocal (index dest) (.simple (.local (index donor)))) (code index rest)

theorem source_items_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (steps : List (Source.Idx Γ .bool × Source.Idx Γ .bool)) (s : Source.EMState E Γ) :
    (Source.execItems G F (fuel+steps.length+3) nps ph (R := R) (M := M) (k := k)
      (sourceItems steps) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (sourceAfter steps s.1)),(.nil,s.2)) := by
  induction steps generalizing s with
  | nil => rfl
  | cons step rest ih =>
    rcases step with ⟨dest,donor⟩
    have evalRun : Source.evalE G F (fuel+rest.length+2) (.assign (.local dest) (.local donor)) (plan := none) s =
        (.ok (.val (s.1.get donor)),(s.1.set dest (s.1.get donor),s.2)) :=
      source_assign_local_run G F (fuel+rest.length) s dest donor _ rfl
    have sub : (Source.EM.sub s.1 (Source.evalE G F (fuel+rest.length+2)
        (.assign (.local dest) (.local donor)))).run (.nil,s.2) =
        (.ok (.val (s.1.get donor),s.1.set dest (s.1.get donor)),(.nil,s.2)) := by
      simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,evalRun]
    have headRun : (Source.execS G F (fuel+rest.length+3) nps ph (R := R) (M := M) (k := k)
        (.expr (.assign (.local dest) (.local donor))) s.1).run (.nil,s.2) =
        (.ok (Source.Out.normal (s.1.set dest (s.1.get donor))),(.nil,s.2)) := by
      rw [Source.execS,Source.Hoare.run_bind,sub]
      rfl
    change (Source.execItems G F ((fuel+rest.length+3)+1) nps ph
      (.stmt (.expr (.assign (.local dest) (.local donor))) (sourceItems rest)) s.1).run (.nil,s.2) = _
    rw [Source.execItems,Source.Hoare.run_bind,headRun]
    dsimp only
    rw [Source.Hoare.run_bind,ih (s.1.set dest (s.1.get donor),s.2)]
    rfl

theorem source_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (steps : List (Source.Idx Γ .bool × Source.Idx Γ .bool)) (s : Source.EMState E Γ) :
    (Source.execS G F (fuel+steps.length+4) nps ph (R := R) (M := M) (k := k)
      (statement steps) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (sourceAfter steps s.1)),(.nil,s.2)) := by
  rw [statement,Source.execS,Source.Hoare.run_bind,source_items_run]
  simp only [Source.Out.close,ReturnTail.source_locals_restore_self]
  rfl

theorem target_run {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (index : Source.Idx srcΓ .bool → Idx Γ (.val .bool))
    (steps : List (Source.Idx srcΓ .bool × Source.Idx srcΓ .bool)) (target : State C Γ) :
    (code index steps).run target = .ok ⟨targetAfter index steps target,List.prefix_refl _⟩ := by
  induction steps generalizing target with
  | nil => rfl
  | cons step rest ih =>
    rcases step with ⟨dest,donor⟩
    rw [code,Prog.run_cons_ok (show (Stmt.assignLocal (index dest)
      (.simple (.local (index donor)))).run target =
      .ok ⟨target.setLocal (index dest) (TEnv.get (index donor) target.env),List.prefix_refl _⟩ from rfl),ih]
    rfl

theorem related_fold {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {H : HTy} {Γ : Ctx}
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C H → Prop)
    (index : Source.Idx srcΓ .bool → Idx Γ (.val .bool))
    (maps : ∀ i, m.slot i = ⟨.val .bool,index i⟩)
    (steps : List (Source.Idx srcΓ .bool × Source.Idx srcΓ .bool))
    (source : Source.Locals D srcΓ) (target : TEnv C H Γ) (aligned : m.Related R source target) :
    m.Related R (sourceAfter steps source) (targetEnvAfter index steps target) := by
  induction steps generalizing source target with
  | nil => exact aligned
  | cons step rest ih =>
    rcases step with ⟨dest,donor⟩
    have next : m.Related R (source.set dest (source.get donor))
        (TEnv.set (index dest) (TEnv.get (index donor) target) target) := by
      intro τ i
      exact ContextMap.related_assign m R source target aligned dest donor
        (index dest) (index donor) (maps dest) (maps donor) i
    intro τ i
    exact ih _ _ @next i

theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M : Bool} {k : Source.SCtx}
    (steps : List (Source.Idx srcΓ .bool × Source.Idx srcΓ .bool))
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (Rel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (index : Source.Idx srcΓ .bool → Idx Γ (.val .bool))
    (maps : ∀ i, m.slot i = ⟨.val .bool,index i⟩) (aligned : m.Related Rel source.1 target.env) :
    (Source.execS G F (fuel+steps.length+4) nps ph (R := returns) (M := M) (k := k)
      (statement steps) source.1).run (.nil,source.2) =
      (.ok (Source.Out.normal (sourceAfter steps source.1)),(.nil,source.2)) ∧
    (code index steps).run target = .ok ⟨targetAfter index steps target,List.prefix_refl _⟩ ∧
    m.Related Rel (sourceAfter steps source.1) (targetAfter index steps target).env ∧
    (targetAfter index steps target).glob = target.glob := by
  exact ⟨source_run G F fuel nps ph steps source,target_run index steps target,
    related_fold m Rel index maps steps source.1 target.env aligned,rfl⟩

theorem source_zero {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (steps : List (Source.Idx Γ .bool × Source.Idx Γ .bool)) (locals : Source.Locals E.layout Γ) :
    Source.execS G F 0 nps ph (R := R) (M := M) (k := k) (statement steps) locals =
      Source.EM.halt .timeout := by rfl

end Solidity.Lowering.G19.AssignmentBlocks
