import Solidity.Lowering.G17.ShortCircuitSource
import Solidity.Lowering.V07.ConditionalAssignments

/-! Effectful Boolean conditional composition through the existing P12
condition contract. Only the selected branch runs, at the condition's reached
state. This does not supply admission/origin or fuel/stuck adequacy and is
not a whole-pass theorem or a claim about non-Boolean conditional results. -/
namespace Solidity.Lowering.G17
open V07 V07.P12NextInterface
variable {C : Contract} {Γ : Ctx}

private def selectedCode (branch : DeferredSource.Operand C Γ (.prim .bool)) :
    Prog C (.val .bool :: Γ) (.val .bool :: Γ) :=
  .cons (storeOperand .here (branch.wk (.drop .refl))) .nil

private theorem selected_run (branch : DeferredSource.Operand C Γ (.prim .bool))
    (target : State C Γ) (b : Bool) :
    (selectedCode branch).runC (target.push (t := .val .bool) b) =
      (branch.run target).map (fun (out,value) => match value with
        | .prim c => (⟨out.st.push (t := .val .bool) c,out.ext⟩ : Out C target.H (.val .bool :: Γ))) := by
  have single := V07.singleton_run (target.push (t := .val .bool) b)
    (storeOperand .here (branch.wk (.drop .refl)))
  simp only [Prog.run,Stmt.run,Prog.runR_eq,Stmt.runR_eq] at single
  change (selectedCode branch).runC (target.push (t := .val .bool) b) = _ at single
  rw [single]
  simpa only [Stmt.run,Stmt.runR_eq] using store_fresh_run branch target b

private def choiceCode (yes no : DeferredSource.Operand C Γ (.prim .bool)) :
    Prog C (.val .bool :: Γ) (.val .bool :: Γ) :=
  .cons (.ite (.simple (.local .here)) (selectedCode yes) (selectedCode no)) .nil

private theorem choice_run (yes no : DeferredSource.Operand C Γ (.prim .bool))
    (target : State C Γ) (b : Bool) :
    (choiceCode yes no).runC (target.push (t := .val .bool) b) =
      ((if b = true then yes else no).run target).map (fun (out,value) => match value with
        | .prim c => (⟨out.st.push (t := .val .bool) c,out.ext⟩ : Out C target.H (.val .bool :: Γ))) := by
  cases b
  all_goals
    change TRun.seq (TRun.ite (.simple (.local .here)) (selectedCode yes).ext
      (selectedCode yes).runC (selectedCode no).ext (selectedCode no).runC)
      TRun.nil (target.push (t := .val .bool) _) = _
    unfold TRun.seq TRun.ite
    simp only [Val.evalT,Simple.evalT,TEnv.get,boolT,
      Bool.false_eq_true,if_false,if_true,bind,Except.bind]
    have ys : (selectedCode yes).ext = .refl := Subsingleton.elim _ _
    have ns : (selectedCode no).ext = .refl := Subsingleton.elim _ _
    simp only [ys,ns,selected_run]
    simp only [State.push,if_true,if_false,Bool.false_eq_true]
  case false =>
    cases run : no.run target with
    | error err => rfl
    | ok result =>
      obtain ⟨out,value⟩ := result
      cases value with
      | prim c => rfl
  case true =>
    cases run : yes.run target with
    | error err => rfl
    | ok result =>
      obtain ⟨out,value⟩ := result
      cases value with
      | prim c => rfl

def conditionalOperand (condition yes no : DeferredSource.Operand C Γ (.prim .bool)) :
    DeferredSource.Operand C Γ (.prim .bool) :=
  ⟨.val .bool :: Γ,
    .cons (.declLocal .bool (.user "g17_choice") none)
      (.cons (storeOperand .here (condition.wk (.drop .refl))) (choiceCode yes no)),
    .val (.simple (.local .here))⟩

/-- Evaluate the condition once, then exactly one branch, retaining all caller
writes, heap growth and halts without any branch-success premise. -/
theorem conditionalOperand_run (condition yes no : DeferredSource.Operand C Γ (.prim .bool))
    (target : State C Γ) :
    (conditionalOperand condition yes no).run target = (do
      let (a,value) ← condition.run target
      match value with
      | .prim b =>
        let (z,value) ← (if b = true then yes else no).run a.st
        pure ((⟨z.st,a.ext.trans z.ext⟩ : Out C target.H Γ),value)) := by
  change (do
    let a ← (conditionalOperand condition yes no).code.run target
    let v ← (conditionalOperand condition yes no).value.valueT a.st
    pure ((⟨a.st.drop (conditionalOperand condition yes no).code.ext,a.ext⟩ : Out C target.H Γ),v)) = _
  have scope : (conditionalOperand condition yes no).code.ext = (.push .refl : Ext Γ (.val .bool :: Γ)) :=
    Subsingleton.elim _ _
  rw [scope]
  simp only [Prog.run,Prog.runR_eq]
  change (do
    let a ← TRun.seq (TRun.declLocal .bool none)
      (TRun.seq (storeOperand .here (condition.wk (.drop .refl))).runC (choiceCode yes no).runC) target
    let v ← (Src.val (.simple (.local .here)) : Src C (.val .bool :: Γ) (.prim .bool)).valueT a.st
    pure ((⟨a.st.drop (.push .refl),a.ext⟩ : Out C target.H Γ),v)) = _
  have firstRun := store_fresh_run condition target false
  simp only [Stmt.run,Stmt.runR_eq] at firstRun
  have initial : TRun.declLocal .bool none target =
      .ok (⟨target.push (t := .val .bool) false,List.prefix_refl _⟩) := by rfl
  unfold TRun.seq
  rw [initial]
  dsimp only []
  rw [firstRun]
  cases first : condition.run target with
  | error err => rfl
  | ok result =>
    obtain ⟨a,value⟩ := result
    cases value with
    | prim b =>
      dsimp only [Except.map,bind,Except.bind]
      rw [choice_run]
      cases second : (if b = true then yes else no).run a.st with
      | error err => rfl
      | ok result =>
        obtain ⟨z,value⟩ := result
        cases value with
        | prim c => rfl

variable {E : Source.Env} {srcΓ : Source.RCtx}

private theorem source_choice_step (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source middle : Source.EMState E srcΓ) (b : Bool)
    (condition yes no : Source.RExpr E srcΓ .bool)
    (conditionRun : (Source.evalE G F fuel condition).run source = (.ok (.val (.bool b)),middle)) :
    (Source.evalE G F (fuel+1) (.cond condition yes no)).run source =
      (Source.evalE G F fuel (if b then yes else no)).run middle := by
  rw [Source.evalE,Source.Hoare.run_bind,conditionRun]
  dsimp only []
  rw [Source.Hoare.run_bind,V07.source_getV_run]
  cases b <;> rfl

private theorem source_choice_error (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source middle : Source.EMState E srcΓ) (halt : Source.Halt)
    (condition yes no : Source.RExpr E srcΓ .bool)
    (conditionRun : (Source.evalE G F fuel condition).run source = (.error halt,middle)) :
    (Source.evalE G F (fuel+1) (.cond condition yes no)).run source = (.error halt,middle) := by
  rw [Source.evalE,Source.Hoare.run_bind,conditionRun]

/-- Compose independent Boolean condition/branch contracts at their actual
reached states. No execution law for the complete conditional is a premise. -/
def conditionalCondition (G : Source.Glob E) (F : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C)
    (condition yes no : Source.RExpr E srcΓ .bool)
    (c : Condition G F m values worlds condition)
    (y : Condition G F m values worlds yes) (n : Condition G F m values worlds no) :
    Condition G F m values worlds (.cond condition yes no) := by
  refine ⟨conditionalOperand c.operand y.operand n.operand,c.initial_nonempty,?_,?_⟩
  · intro fuel source after target choice aligned run
    cases fuel with
    | zero => cases run
    | succ fuel =>
      cases inner : (Source.evalE G F fuel condition).run source with
      | mk result middle =>
        cases result with
        | error halt => rw [source_choice_error G F fuel source middle halt condition yes no inner] at run; cases run
        | ok value =>
          cases value with
          | val value =>
            obtain ⟨b,rfl⟩ := Source.Val.eq_bool value
            obtain ⟨a,native,post⟩ := c.success fuel source middle target b aligned inner
            rw [source_choice_step G F fuel source middle b condition yes no inner] at run
            let chosen : Condition G F m values worlds (if b then yes else no) :=
              match b with | false => n | true => y
            have selected := chosen.success fuel middle after a.st choice post
            cases b
            all_goals
              obtain ⟨z,branch,reached⟩ := selected run
              refine ⟨⟨z.st,a.ext.trans z.ext⟩,?_,reached⟩
              rw [conditionalOperand_run,native]
              simp only [PrimTy.Denote,bind,Except.bind,if_true,if_false,Bool.false_eq_true] at branch ⊢
              dsimp only [chosen] at branch
              rw [branch]
              rfl
  · intro fuel source after target data aligned run
    cases fuel with
    | zero => cases run
    | succ fuel =>
      cases inner : (Source.evalE G F fuel condition).run source with
      | mk result middle =>
        cases result with
        | error halt =>
          rw [source_choice_error G F fuel source middle halt condition yes no inner] at run
          have same : halt = .revert data := Except.error.inj (congrArg Prod.fst run)
          subst halt
          have native := c.revert fuel source middle target data aligned inner
          rw [conditionalOperand_run,native]
          rfl
        | ok value =>
          cases value with
          | val value =>
            obtain ⟨b,rfl⟩ := Source.Val.eq_bool value
            obtain ⟨a,native,post⟩ := c.success fuel source middle target b aligned inner
            rw [source_choice_step G F fuel source middle b condition yes no inner] at run
            let chosen : Condition G F m values worlds (if b then yes else no) :=
              match b with | false => n | true => y
            have selected := chosen.revert fuel middle after a.st data post
            cases b
            all_goals
              have branch := selected run
              rw [conditionalOperand_run,native]
              simp only [PrimTy.Denote,bind,Except.bind,if_true,if_false,Bool.false_eq_true] at branch ⊢
              dsimp only [chosen] at branch
              rw [branch]

#print axioms source_choice_step
#print axioms source_choice_error
#print axioms conditionalCondition
#print axioms selected_run
#print axioms choice_run
#print axioms conditionalOperand_run
end Solidity.Lowering.G17
