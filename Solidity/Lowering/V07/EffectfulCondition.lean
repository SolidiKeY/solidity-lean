import Solidity.Lowering.V07.ContextMapWrite

/-! P12 EFFECTFUL-CONDITION: actual local/assignment Boolean constructors.
The Boolean clause is an independent VALUE relation. Actual Source and target
prefix runs, reached context alignment and captured choice are DERIVED below.
This is no G19 block/loop/modifier compiler or complete condition producer. -/
namespace Solidity.Lowering.V07

theorem assigned_condition_prefix_run {C : Contract} {Γ : Ctx}
    (target : State C Γ) (i a : Idx Γ (.val .bool)) :
    (assignLocalOperand i a).code.run target =
      .ok (⟨(target.setLocal i (TEnv.get a target.env)).push
        (t := .val .bool) (TEnv.get a target.env),List.prefix_refl _⟩) := by
  change (do
    let value ← (Except.ok (TEnv.get a target.env) : TRes Bool)
    let captured ← (Except.ok (TEnv.get i (TEnv.set i value target.env)) : TRes Bool)
    pure (⟨(target.setLocal i value).push (t := .val .bool) captured,List.prefix_refl _⟩ :
      Out C target.H (.val .bool :: Γ))) = _
  simp only [TEnv.get_set]
  rfl

/-- The prefix's Boolean is read BEFORE its fresh capture binder is dropped.
All old heterogeneous bindings remain aligned, including live references. -/
theorem condition_assignment_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      R .bool (.val .bool) v b → v = .bool b)
    (i a : Source.Idx srcΓ .bool) (j b : Idx Γ (.val .bool))
    (writeMap : m.slot i = ⟨.val .bool,j⟩) (readMap : m.slot a = ⟨.val .bool,b⟩) :
    (Source.evalE G F (fuel+2) (.assign (.local i) (.local a))).run source =
      (.ok (.val (.bool (TEnv.get b target.env))),
        (source.1.set i (.bool (TEnv.get b target.env)),source.2)) ∧
    (assignLocalOperand j b).code.run target =
      .ok (⟨(target.setLocal j (TEnv.get b target.env)).push
        (t := .val .bool) (TEnv.get b target.env),List.prefix_refl _⟩) ∧
    (.simple (.local .here) : Val C (.val .bool :: Γ) .bool).evalT
      ((target.setLocal j (TEnv.get b target.env)).push (t := .val .bool) (TEnv.get b target.env)) =
        .ok (TEnv.get b target.env) ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R
      (source.1.set i (.bool (TEnv.get b target.env)))
      ((target.setLocal j (TEnv.get b target.env)).push (t := .val .bool) (TEnv.get b target.env)).env ∧
    ((target.setLocal j (TEnv.get b target.env)).push (t := .val .bool) (TEnv.get b target.env)).glob =
      target.glob := by
  have rhsRel := ContextMap.value_at m R source.1 target.env aligned a b readMap
  have read := boolReflect _ _ rhsRel
  have post : m.Related R (source.1.set i (source.1.get a))
      (TEnv.set j (TEnv.get b target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i a j b writeMap readMap
  rw [read] at post
  refine ⟨source_assign_local_run G F fuel source i a _ read,
    assigned_condition_prefix_run target j b,rfl,?_,rfl⟩
  intro τ k
  exact post k

/-- Direct ordinary-run interface when a consumer uses Operand.run instead
of its still-scoped prefix. Caller effects survive private temporary removal. -/
theorem assigned_condition_operand_run {C : Contract} {Γ : Ctx}
    (target : State C Γ) (i a : Idx Γ (.val .bool)) :
    (assignLocalOperand i a).run target =
      .ok (⟨target.setLocal i (TEnv.get a target.env),List.prefix_refl _⟩,
        .prim (TEnv.get a target.env)) :=
  assign_local_operand_run target i a _ rfl

theorem assigned_condition_extension {C : Contract} {Γ Δ : Ctx}
    (target : State C Γ) (i a : Idx Γ (.val .bool)) (thin : Thin Γ Δ)
    (extra : TEnv C target.H Δ) :
    ((assignLocalOperand i a).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨target.setLocal i (TEnv.get a target.env),List.prefix_refl _⟩ :
        Out C target.H Γ),SVal.prim (TEnv.get a target.env))) := by
  rw [DeferredSource.Operand.run_wk,assigned_condition_operand_run]

end Solidity.Lowering.V07
