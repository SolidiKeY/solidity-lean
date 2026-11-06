import Solidity.Lowering.V07.AllAliasPair
import Solidity.Lowering.V07.EffectfulCondition

/-! Actual effectful Boolean short circuit. `conj` selects existing and/or;
there is no new syntax, operation AST, state carrier or source evaluator. -/
namespace Solidity.Lowering.V07

def needsRight (conj left : Bool) : Bool := if conj then left else !left

theorem source_getV_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (source : Source.EMState E Γ) (v : Source.Val E.layout τ) :
    (Source.getV (.val v)).run source = (.ok v,source) := rfl

theorem source_short_assign_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (conj : Bool) (i a j b : Source.Idx Γ .bool) (x z : Bool)
    (readA : source.1.get a = .bool x) (readB : source.1.get b = .bool z) :
    (Source.evalE G F (fuel+3) (.binary (if conj then .and else .or)
      (.assign (.local i) (.local a)) (.assign (.local j) (.local b)))).run source =
      (.ok (.val (.bool (if needsRight conj x then
          (if i.toNat = b.toNat then x else z) else x))),
        (if needsRight conj x then
          ((source.1.set i (.bool x)).set j
            (.bool (if i.toNat = b.toNat then x else z)),source.2)
        else (source.1.set i (.bool x),source.2))) := by
  have reached : (source.1.set i (.bool x)).get b =
      .bool (if i.toNat = b.toNat then x else z) := by
    rw [source_written_read,readB]
    split <;> rfl
  cases conj <;> cases x
  all_goals
    rw [Source.evalE]
    simp only [reduceCtorEq, decide_true, decide_false, Bool.true_or, Bool.false_or,
      Bool.false_eq_true, if_true, if_false]
    rw [Source.Hoare.run_bind,source_assign_local_run G F fuel source i a _ readA]
    dsimp only
    rw [Source.Hoare.run_bind,source_getV_run]
    dsimp only
    simp only [Source.Val.key,needsRight, Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
      show (0 : Int) ≠ 1 from by decide,
      show (1 : Int) ≠ 0 from by decide, decide_true, decide_false, Bool.false_and, Bool.true_and,
      Bool.false_or, Bool.or_false]
    try rfl
  all_goals
    rw [Source.Hoare.run_bind,source_assign_local_run G F fuel
      (source.1.set i (.bool _),source.2) j b _ reached]
    rfl

/-- The result binder is fresh; the right branch updates it only after its
actual RHS has been read and written to the caller. -/
def shortRight {C : Contract} {Γ : Ctx} (j b : Idx Γ (.val .bool)) :
    Prog C (.val .bool :: Γ) (.val .bool :: Γ) :=
  .cons (.assignLocal (.there j) (.simple (.local (.there b))))
    (.cons (.assignLocal .here (.simple (.local (.there j)))) .nil)

theorem short_right_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (j b : Idx Γ (.val .bool)) (left : Bool) :
    (shortRight j b).run (target.push (t := .val .bool) left) =
      .ok (⟨(target.setLocal j (TEnv.get b target.env)).push
        (t := .val .bool) (TEnv.get b target.env),List.prefix_refl _⟩) := by
  change (do
    let right ← (Except.ok (TEnv.get b target.env) : TRes Bool)
    let captured ← (Except.ok (TEnv.get j (TEnv.set j right target.env)) : TRes Bool)
    pure (⟨(target.setLocal j right).push (t := .val .bool) captured,
      List.prefix_refl _⟩ : Out C target.H (.val .bool :: Γ))) = _
  simp only [TEnv.get_set]
  rfl

def shortAssignPrefix {C : Contract} {Γ : Ctx} (conj : Bool)
    (i a j b : Idx Γ (.val .bool)) : Prog C Γ (.val .bool :: Γ) :=
  .cons (.assignLocal i (.simple (.local a)))
    (.cons (.declLocal .bool (.user "v07_short_left") (some (.simple (.local i))))
      (.cons (.ite (.simple (.local .here))
        (if conj then shortRight j b else .nil)
        (if conj then .nil else shortRight j b)) .nil))

theorem short_assign_prefix_run {C : Contract} {Γ : Ctx}
    (target : State C Γ) (conj : Bool) (i a j b : Idx Γ (.val .bool)) (x : Bool)
    (readA : TEnv.get a target.env = x) :
    (shortAssignPrefix conj i a j b).run target =
      .ok (⟨(if needsRight conj x then
          ((target.setLocal i x).setLocal j (TEnv.get b (TEnv.set i x target.env))).push
            (t := .val .bool) (TEnv.get b (TEnv.set i x target.env))
        else (target.setLocal i x).push (t := .val .bool) x),
        by split <;> exact List.prefix_refl _⟩) := by
  have first : (Stmt.assignLocal i (.simple (.local a))).run target =
      .ok (⟨target.setLocal i x,List.prefix_refl _⟩) := by
    change Except.ok (⟨target.setLocal i (TEnv.get a target.env),List.prefix_refl _⟩ : Out C target.H Γ) = _
    rw [readA]
  have capture : (Stmt.declLocal .bool (.user "v07_short_left") (some (.simple (.local i)))).run
      (target.setLocal i x) = .ok (⟨(target.setLocal i x).push (t := .val .bool) x,List.prefix_refl _⟩) := by
    change Except.ok (⟨(target.setLocal i x).push (t := .val .bool)
      (TEnv.get i (TEnv.set i x target.env)),List.prefix_refl _⟩ : Out C target.H (.val .bool :: Γ)) = _
    rw [TEnv.get_set]
  have branch : (Stmt.ite (.simple (.local .here))
        (if conj then shortRight j b else (Prog.nil : Prog C (.val .bool :: Γ) (.val .bool :: Γ)))
        (if conj then (Prog.nil : Prog C (.val .bool :: Γ) (.val .bool :: Γ)) else shortRight j b)).run
      ((target.setLocal i x).push (t := .val .bool) x) =
      .ok (⟨(if needsRight conj x then
          ((target.setLocal i x).setLocal j (TEnv.get b (TEnv.set i x target.env))).push
            (t := .val .bool) (TEnv.get b (TEnv.set i x target.env))
        else (target.setLocal i x).push (t := .val .bool) x),by split <;> exact List.prefix_refl _⟩) := by
    cases conj <;> cases x
    · change ((shortRight j b).run ((target.setLocal i false).push (t := .val .bool) false)).map
        (fun o => (⟨o.st.drop .refl,o.ext⟩ : Out C target.H (.val .bool :: Γ))) = _
      rw [short_right_run]
      rfl
    · rfl
    · rfl
    · change ((shortRight j b).run ((target.setLocal i true).push (t := .val .bool) true)).map
        (fun o => (⟨o.st.drop .refl,o.ext⟩ : Out C target.H (.val .bool :: Γ))) = _
      rw [short_right_run]
      rfl
  unfold shortAssignPrefix
  rw [Prog.run_cons_ok first,Prog.run_cons_ok capture,Prog.run_cons_ok branch,Prog.run_nil]
  rfl

def shortAssignOperand {C : Contract} {Γ : Ctx} (conj : Bool)
    (i a j b : Idx Γ (.val .bool)) : DeferredSource.Operand C Γ (.prim .bool) :=
  ⟨.val .bool :: Γ,shortAssignPrefix conj i a j b,.val (.simple (.local .here))⟩

theorem short_assign_operand_run {C : Contract} {Γ : Ctx}
    (target : State C Γ) (conj : Bool) (i a j b : Idx Γ (.val .bool)) (x : Bool)
    (readA : TEnv.get a target.env = x) :
    (shortAssignOperand conj i a j b).run target =
      .ok (⟨(if needsRight conj x then
          (target.setLocal i x).setLocal j (TEnv.get b (TEnv.set i x target.env))
        else target.setLocal i x),by split <;> exact List.prefix_refl _⟩,
        .prim (if needsRight conj x then TEnv.get b (TEnv.set i x target.env) else x)) := by
  unfold shortAssignOperand DeferredSource.Operand.run
  rw [short_assign_prefix_run target conj i a j b x readA]
  by_cases h : needsRight conj x = true
  · simp only [if_pos h]
    rfl
  · simp only [if_neg h]
    rfl

/-- Value-level Boolean reflection and the initial heterogeneous context map
supply every initial/reached read. No desired execution or reached alignment is
assumed. The Source state and entire target caller remain explicit. -/
theorem short_assignment_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (c : Bool), R .bool (.val .bool) v c → v = .bool c)
    (conj : Bool) (i a j b : Source.Idx srcΓ .bool) (ti ta tj tb : Idx Γ (.val .bool))
    (mapI : m.slot i = ⟨.val .bool,ti⟩) (mapA : m.slot a = ⟨.val .bool,ta⟩)
    (mapJ : m.slot j = ⟨.val .bool,tj⟩) (mapB : m.slot b = ⟨.val .bool,tb⟩) :
    let x := TEnv.get ta target.env
    let y := TEnv.get tb (TEnv.set ti x target.env)
    let caller := if needsRight conj x then (target.setLocal ti x).setLocal tj y else target.setLocal ti x
    let srcPost := if needsRight conj x then
      ((source.1.set i (.bool x)).set j (.bool y),source.2) else (source.1.set i (.bool x),source.2)
    (Source.evalE G F (fuel+3) (.binary (if conj then .and else .or)
      (.assign (.local i) (.local a)) (.assign (.local j) (.local b)))).run source =
      (.ok (.val (.bool (if needsRight conj x then y else x))),srcPost) ∧
    (shortAssignOperand conj ti ta tj tb).run target =
      .ok (⟨caller,by
          change target.H <+: (if needsRight conj x then
            (target.setLocal ti x).setLocal tj y else target.setLocal ti x).H
          split <;> exact List.prefix_refl _⟩,
        .prim (if needsRight conj x then y else x)) ∧
    m.Related R srcPost.1
      (if needsRight conj x then TEnv.set tj y (TEnv.set ti x target.env)
        else TEnv.set ti x target.env) ∧ caller.glob = target.glob := by
  dsimp only
  have sourceA := boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned a ta mapA)
  have sourceB := boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned b tb mapB)
  have firstRel : m.Related R (source.1.set i (source.1.get a))
      (TEnv.set ti (TEnv.get ta target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i a ti ta mapI mapA
  rw [sourceA] at firstRel
  have reachedRead := boolReflect _ _ (ContextMap.value_at m R
    (source.1.set i (.bool (TEnv.get ta target.env))) (TEnv.set ti (TEnv.get ta target.env) target.env)
    firstRel b tb mapB)
  have secondRel : m.Related R
      ((source.1.set i (.bool (TEnv.get ta target.env))).set j
        ((source.1.set i (.bool (TEnv.get ta target.env))).get b))
      (TEnv.set tj (TEnv.get tb (TEnv.set ti (TEnv.get ta target.env) target.env))
        (TEnv.set ti (TEnv.get ta target.env) target.env)) :=
    ContextMap.related_assign m R
      (source.1.set i (.bool (TEnv.get ta target.env))) (TEnv.set ti (TEnv.get ta target.env) target.env)
      firstRel j b tj tb mapJ mapB
  rw [reachedRead] at secondRel
  have rhsEq : (if i.toNat = b.toNat then TEnv.get ta target.env else TEnv.get tb target.env) =
      TEnv.get tb (TEnv.set ti (TEnv.get ta target.env) target.env) := by
    have hr := source_written_read source.1 i b (.bool (TEnv.get ta target.env))
    rw [sourceB,reachedRead] at hr
    by_cases h : i.toNat = b.toNat
    · simp only [if_pos h] at hr ⊢
      exact (Source.Val.bool.inj hr).symm
    · simp only [if_neg h] at hr ⊢
      exact (Source.Val.bool.inj hr).symm
  have sourceRun := source_short_assign_run G F fuel source conj i a j b _ _ sourceA sourceB
  rw [rhsEq] at sourceRun
  refine ⟨sourceRun,short_assign_operand_run target conj ti ta tj tb _ rfl,?_,?_⟩
  · by_cases h : needsRight conj (TEnv.get ta target.env) = true
    · simpa only [if_pos h,State.setLocal] using secondRel
    · simpa only [if_neg h,State.setLocal] using firstRel
  · split <;> rfl

theorem short_assign_extension {C : Contract} {Γ Δ : Ctx}
    (target : State C Γ) (conj : Bool) (i a j b : Idx Γ (.val .bool))
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((shortAssignOperand conj i a j b).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨(if needsRight conj (TEnv.get a target.env) then
          (target.setLocal i (TEnv.get a target.env)).setLocal j
            (TEnv.get b (TEnv.set i (TEnv.get a target.env) target.env))
        else target.setLocal i (TEnv.get a target.env)),by split <;> exact List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (if needsRight conj (TEnv.get a target.env) then
          TEnv.get b (TEnv.set i (TEnv.get a target.env) target.env) else TEnv.get a target.env))) := by
  rw [DeferredSource.Operand.run_wk,short_assign_operand_run target conj i a j b _ rfl]

/-- A skipped RHS may be arbitrary, including an operation which would fail.
No RHS purity or successful-run premise is needed when it is not evaluated. -/
theorem source_short_skip {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (conj : Bool) (i a : Source.Idx Γ .bool) (x : Bool) (rhs : Source.RExpr E Γ .bool)
    (readA : source.1.get a = .bool x) (skip : needsRight conj x = false) :
    (Source.evalE G F (fuel+3) (.binary (if conj then .and else .or)
      (.assign (.local i) (.local a)) rhs)).run source =
      (.ok (.val (.bool x)),(source.1.set i (.bool x),source.2)) := by
  cases conj <;> cases x <;>
    simp only [needsRight,Bool.false_eq_true,if_false,if_true,Bool.not_false,Bool.not_true,
      reduceCtorEq] at skip
  all_goals
    rw [Source.evalE]
    simp only [reduceCtorEq,decide_true,decide_false,Bool.true_or,Bool.false_or,
      Bool.false_eq_true,if_true,if_false]
    rw [Source.Hoare.run_bind,source_assign_local_run G F fuel source i a _ readA]
    dsimp only
    rw [Source.Hoare.run_bind,source_getV_run]
    rfl

end Solidity.Lowering.V07
