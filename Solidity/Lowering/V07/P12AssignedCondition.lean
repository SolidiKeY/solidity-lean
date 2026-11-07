import Solidity.Lowering.V07.P12NextInterface

/-! A concrete constructor of the published P12 condition contract for local
Boolean assignment. This is a clause producer, not admitted syntax selection. -/
namespace Solidity.Lowering.V07.P12AssignedCondition
open P12NextInterface

theorem source_zero {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (source : Source.EMState E Γ) (i a : Source.Idx Γ .bool) :
    (Source.evalE G F 0 (.assign (.local i) (.local a))).run source = (.error .timeout,source) := by
  rfl

theorem source_one {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (source : Source.EMState E Γ) (i a : Source.Idx Γ .bool) :
    (Source.evalE G F 1 (.assign (.local i) (.local a))).run source = (.error .timeout,source) := by
  rfl

theorem source_success {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source after : Source.EMState E Γ) (i a : Source.Idx Γ .bool)
    (value choice : Bool) (read : source.1.get a = .bool value)
    (run : (Source.evalE G F fuel (.assign (.local i) (.local a))).run source =
      (.ok (.val (.bool choice)),after)) :
    choice = value ∧ after = (source.1.set i (.bool value),source.2) := by
  cases fuel with
  | zero => rw [source_zero] at run; cases run
  | succ fuel => cases fuel with
    | zero => rw [source_one] at run; cases run
    | succ fuel =>
      rw [source_assign_local_run G F fuel source i a (.bool value) read] at run
      have result := congrArg Prod.fst run
      have state := congrArg Prod.snd run
      have same : value = choice := by
        have observed : some value = some choice := congrArg
          (fun out : Source.R (Source.RVal E.layout .bool) =>
            match out with | .ok (.val (.bool c)) => some c | _ => none) result
        exact Option.some.inj observed
      exact ⟨same.symm,state.symm⟩

theorem source_not_revert {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source after : Source.EMState E Γ) (i a : Source.Idx Γ .bool)
    (value : Bool) (read : source.1.get a = .bool value) (data : Roadmap.Bytes) :
    (Source.evalE G F fuel (.assign (.local i) (.local a))).run source ≠ (.error (.revert data),after) := by
  intro run
  cases fuel with
  | zero => rw [source_zero] at run; cases run
  | succ fuel => cases fuel with
    | zero => rw [source_one] at run; cases run
    | succ fuel =>
      rw [source_assign_local_run G F fuel source i a (.bool value) read] at run
      cases run

theorem aligned_assignment {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (values : ValueRelation E C) (worlds : WorldRelation E C)
    (source : Source.EMState E srcΓ) (target : State C Γ) (aligned : Aligned m values worlds source target)
    (i a : Source.Idx srcΓ .bool) (j b : Idx Γ (.val .bool))
    (writeMap : m.slot i = ⟨.val .bool,j⟩) (readMap : m.slot a = ⟨.val .bool,b⟩) :
    Aligned m values worlds (source.1.set i (source.1.get a),source.2)
      (target.setLocal j (TEnv.get b target.env)) := by
  exact ⟨aligned.1,ContextMap.related_assign m (values source.2 target.glob)
    source.1 target.env aligned.2 i a j b writeMap readMap⟩

def assignment {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C)
    (boolReflect : ∀ (source : Source.St E) (target : State C [])
      (v : Source.Val E.layout .bool) (c : Bool), values source target .bool (.val .bool) v c → v = .bool c)
    (inhabited : ∃ source target, Aligned m values worlds source target)
    (i a : Source.Idx srcΓ .bool) (j b : Idx Γ (.val .bool))
    (writeMap : m.slot i = ⟨.val .bool,j⟩) (readMap : m.slot a = ⟨.val .bool,b⟩) :
    Condition G F m values worlds (.assign (.local i) (.local a)) := by
  refine ⟨assignLocalOperand j b,inhabited,?_,?_⟩
  · intro fuel source after target choice aligned run
    have read : source.1.get a = .bool (TEnv.get b target.env) :=
      boolReflect source.2 target.glob _ _ (ContextMap.value_at m (values source.2 target.glob)
        source.1 target.env aligned.2 a b readMap)
    obtain ⟨same,post⟩ := source_success G F fuel source after i a _ choice read run
    subst choice
    subst after
    refine ⟨⟨target.setLocal j (TEnv.get b target.env),List.prefix_refl _⟩,
      assigned_condition_operand_run target j b,?_⟩
    have reached := aligned_assignment m values worlds source target aligned i a j b writeMap readMap
    rw [read] at reached
    exact reached
  · intro fuel source after target data aligned run
    have read : source.1.get a = .bool (TEnv.get b target.env) :=
      boolReflect source.2 target.glob _ _ (ContextMap.value_at m (values source.2 target.glob)
        source.1 target.env aligned.2 a b readMap)
    exact False.elim (source_not_revert G F fuel source after i a _ read data run)

/-- info: 'Solidity.Lowering.V07.P12AssignedCondition.source_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedCondition.source_zero

/-- info: 'Solidity.Lowering.V07.P12AssignedCondition.source_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedCondition.source_one

/-- info: 'Solidity.Lowering.V07.P12AssignedCondition.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedCondition.source_success

/-- info: 'Solidity.Lowering.V07.P12AssignedCondition.source_not_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedCondition.source_not_revert

/-- info: 'Solidity.Lowering.V07.P12AssignedCondition.aligned_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedCondition.aligned_assignment

/-- info: 'Solidity.Lowering.V07.P12AssignedCondition.assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12AssignedCondition.assignment

end Solidity.Lowering.V07.P12AssignedCondition
