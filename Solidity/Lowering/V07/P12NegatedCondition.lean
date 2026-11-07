import Solidity.Lowering.V07.P12NextInterface
import Solidity.Source.ValueProgress

/-! Logical negation composes the published condition contract without
re-running its operand or changing its caller effects. Source horizons remain
operational approximations, not an admission unrolling bound. -/
namespace Solidity.Lowering.V07.P12NegatedCondition
open P12NextInterface

def notValue {C : Contract} {Γ : Ctx} : Src C Γ (.prim .bool) → Src C Γ (.prim .bool)
  | .val value => .val (.unop .not rfl rfl value)

def operand {C : Contract} {Γ : Ctx} (e : DeferredSource.Operand C Γ (.prim .bool)) :
    DeferredSource.Operand C Γ (.prim .bool) := ⟨e.tailCtx,e.code,notValue e.value⟩

theorem operand_code {C : Contract} {Γ : Ctx} (e : DeferredSource.Operand C Γ (.prim .bool)) :
    (operand e).code = e.code := by
  rfl

theorem operand_run {C : Contract} {Γ : Ctx} (e : DeferredSource.Operand C Γ (.prim .bool)) (target : State C Γ) :
    (operand e).run target = (e.run target).map (fun (out,value) =>
      (out,match value with | .prim b => SVal.prim (!b))) := by
  obtain ⟨Δ,code,value⟩ := e
  cases value with
  | val value =>
    unfold operand notValue DeferredSource.Operand.run
    generalize preludeRun : code.run target = result
    cases result with
    | error err => rfl
    | ok out =>
      cases read : value.evalT out.st with
      | error err => simp only [Src.valueT,Val.evalT,bind,Except.bind,read]; rfl
      | ok b => simp only [Src.valueT,Val.evalT,bind,Except.bind,read]; rfl

theorem operand_success {C : Contract} {Γ : Ctx} (e : DeferredSource.Operand C Γ (.prim .bool))
    (target : State C Γ) (out : Out C target.H Γ) (value : Bool)
    (run : e.run target = .ok (out,.prim value)) :
    (operand e).run target = .ok (out,.prim (!value)) := by
  rw [operand_run,run]
  rfl

theorem operand_error {C : Contract} {Γ : Ctx} (e : DeferredSource.Operand C Γ (.prim .bool))
    (target : State C Γ) (err : THalt) (run : e.run target = .error err) :
    (operand e).run target = .error err := by
  rw [operand_run,run]
  rfl

theorem double_negate_run {C : Contract} {Γ : Ctx} (e : DeferredSource.Operand C Γ (.prim .bool))
    (target : State C Γ) : (operand (operand e)).run target = e.run target := by
  rw [operand_run,operand_run]
  cases run : e.run target with
  | error err => rfl
  | ok result =>
    obtain ⟨out,value⟩ := result
    cases value with
    | prim b => cases b <;> rfl

theorem source_zero {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (source : Source.EMState E Γ) (expr : Source.RExpr E Γ .bool) :
    (Source.evalE G F 0 (.unary .not expr)).run source = (.error .timeout,source) := by
  rfl

theorem source_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source after : Source.EMState E Γ) (expr : Source.RExpr E Γ .bool) (value : Bool)
    (run : (Source.evalE G F fuel expr).run source = (.ok (.val (.bool value)),after)) :
    (Source.evalE G F (fuel+1) (.unary .not expr)).run source = (.ok (.val (.bool (!value))),after) := by
  rw [Source.evalE,Source.Hoare.run_bind,run]
  rfl

theorem source_error {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source after : Source.EMState E Γ) (expr : Source.RExpr E Γ .bool) (halt : Source.Halt)
    (run : (Source.evalE G F fuel expr).run source = (.error halt,after)) :
    (Source.evalE G F (fuel+1) (.unary .not expr)).run source = (.error halt,after) := by
  rw [Source.evalE,Source.Hoare.run_bind,run]

theorem source_success {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source after : Source.EMState E Γ) (expr : Source.RExpr E Γ .bool) (choice : Bool)
    (run : (Source.evalE G F (fuel+1) (.unary .not expr)).run source = (.ok (.val (.bool choice)),after)) :
    ∃ value, (Source.evalE G F fuel expr).run source = (.ok (.val (.bool value)),after) ∧ choice = !value := by
  cases inner : (Source.evalE G F fuel expr).run source with
  | mk result reached =>
    cases result with
    | error halt => rw [source_error G F fuel source reached expr halt inner] at run; cases run
    | ok value => cases value with
      | val value =>
          obtain ⟨b,rfl⟩ := Source.Val.eq_bool value
          rw [source_run G F fuel source reached expr b inner] at run
          have post : reached = after := congrArg Prod.snd run
          have observed : some (!b) = some choice := congrArg
            (fun out : Source.R (Source.RVal E.layout .bool) =>
              match out with | .ok (.val (.bool c)) => some c | _ => none) (congrArg Prod.fst run)
          refine ⟨b,?_,(Option.some.inj observed).symm⟩
          rw [post]

theorem source_revert {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source after : Source.EMState E Γ) (expr : Source.RExpr E Γ .bool) (data : Roadmap.Bytes)
    (run : (Source.evalE G F (fuel+1) (.unary .not expr)).run source = (.error (.revert data),after)) :
    (Source.evalE G F fuel expr).run source = (.error (.revert data),after) := by
  cases inner : (Source.evalE G F fuel expr).run source with
  | mk result reached =>
    cases result with
    | error halt =>
      rw [source_error G F fuel source reached expr halt inner] at run
      have same : halt = .revert data := Except.error.inj (congrArg Prod.fst run)
      have post : reached = after := congrArg Prod.snd run
      simp only [same,post]
    | ok value => cases value with
      | val value =>
          obtain ⟨b,rfl⟩ := Source.Val.eq_bool value
          rw [source_run G F fuel source reached expr b inner] at run
          cases run

def negate {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C) (expr : Source.RExpr E srcΓ .bool)
    (input : Condition G F m values worlds expr) : Condition G F m values worlds (.unary .not expr) := by
  refine ⟨operand input.operand,input.initial_nonempty,?_,?_⟩
  · intro fuel source after target choice aligned run
    cases fuel with
    | zero => rw [source_zero] at run; cases run
    | succ fuel =>
      obtain ⟨value,inner,choiceEq⟩ := source_success G F fuel source after expr choice run
      obtain ⟨out,native,reached⟩ := input.success fuel source after target value aligned inner
      refine ⟨out,?_,reached⟩
      rw [choiceEq]
      exact operand_success input.operand target out value native
  · intro fuel source after target data aligned run
    cases fuel with
    | zero => rw [source_zero] at run; cases run
    | succ fuel =>
      have inner := source_revert G F fuel source after expr data run
      exact operand_error input.operand target (THalt.ofData data)
        (input.revert fuel source after target data aligned inner)

/-- info: 'Solidity.Lowering.V07.P12NegatedCondition.operand_code' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedCondition.operand_code

/-- info: 'Solidity.Lowering.V07.P12NegatedCondition.operand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedCondition.operand_run

/-- info: 'Solidity.Lowering.V07.P12NegatedCondition.operand_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedCondition.operand_success

/-- info: 'Solidity.Lowering.V07.P12NegatedCondition.operand_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedCondition.operand_error

/-- info: 'Solidity.Lowering.V07.P12NegatedCondition.double_negate_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedCondition.double_negate_run

/-- info: 'Solidity.Lowering.V07.P12NegatedCondition.source_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedCondition.source_zero

/-- info: 'Solidity.Lowering.V07.P12NegatedCondition.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedCondition.source_run

/-- info: 'Solidity.Lowering.V07.P12NegatedCondition.source_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedCondition.source_error

/-- info: 'Solidity.Lowering.V07.P12NegatedCondition.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedCondition.source_success

/-- info: 'Solidity.Lowering.V07.P12NegatedCondition.source_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedCondition.source_revert

/-- info: 'Solidity.Lowering.V07.P12NegatedCondition.negate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedCondition.negate

end Solidity.Lowering.V07.P12NegatedCondition
