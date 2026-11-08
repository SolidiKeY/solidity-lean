import Solidity.Lowering.G17.ShortCircuit
import Solidity.Source.ValueProgress

/-! Compositional Source-to-native lazy Boolean lowering using the published
P12 condition contract. The operands' existing producers supply their own
success/revert proofs; no execution of the whole binary is a premise.
This retains P12's explicit boundary: no admission/origin producer, Source
fuel/stuck adequacy, physical gas, callback oracle or whole-pass claim. -/
namespace Solidity.Lowering.G17
open V07 V07.P12NextInterface
variable {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}

private theorem source_step (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source middle : Source.EMState E srcΓ) (conj b : Bool)
    (left right : Source.RExpr E srcΓ .bool)
    (leftRun : (Source.evalE G F fuel left).run source = (.ok (.val (.bool b)),middle)) :
    (Source.evalE G F (fuel+1) (.binary (if conj then .and else .or) left right)).run source =
      if needsRight conj b then (Source.evalE G F fuel right).run middle
      else (.ok (.val (.bool b)),middle) := by
  cases conj <;> cases b
  all_goals
    rw [Source.evalE]
    simp only [reduceCtorEq,decide_true,decide_false,Bool.true_or,Bool.false_or,
      Bool.false_eq_true,if_true,if_false]
    rw [Source.Hoare.run_bind,leftRun]
    dsimp only []
    rw [Source.Hoare.run_bind,V07.source_getV_run]
    dsimp only []
    simp only [Source.Val.key,needsRight,Bool.false_eq_true,if_false,if_true,Bool.not_false,Bool.not_true,
      show (0 : Int) ≠ 1 from by decide,show (1 : Int) ≠ 0 from by decide,
      decide_true,decide_false,Bool.false_and,Bool.true_and,Bool.false_or,Bool.or_false]
    first | rfl | skip
  all_goals
    cases inner : (Source.evalE G F fuel right).run middle with
    | mk result after =>
      cases result with
      | error halt => rw [Source.Hoare.run_bind,inner]
      | ok value =>
        cases value with
        | val v => rw [Source.Hoare.run_bind,inner]; rfl

private theorem source_error (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source middle : Source.EMState E srcΓ) (conj : Bool)
    (left right : Source.RExpr E srcΓ .bool) (halt : Source.Halt)
    (leftRun : (Source.evalE G F fuel left).run source = (.error halt,middle)) :
    (Source.evalE G F (fuel+1) (.binary (if conj then .and else .or) left right)).run source =
      (.error halt,middle) := by
  cases conj
  all_goals
    rw [Source.evalE]
    simp only [reduceCtorEq,decide_true,decide_false,Bool.true_or,Bool.false_or,
      Bool.false_eq_true,if_true,if_false]
    rw [Source.Hoare.run_bind,leftRun]

/-- One family constructor for both lazy Boolean operators. The RHS producer
is invoked at the actual reached state only on the taken branch. Independent
world/value relations and all caller bindings are retained through composition. -/
def shortCondition (G : Source.Glob E) (F : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C) (conj : Bool)
    (left right : Source.RExpr E srcΓ .bool)
    (l : Condition G F m values worlds left) (r : Condition G F m values worlds right) :
    Condition G F m values worlds (.binary (if conj then .and else .or) left right) := by
  refine ⟨shortOperand conj l.operand r.operand,l.initial_nonempty,?_,?_⟩
  · intro fuel source after target choice aligned run
    cases fuel with
    | zero => cases run
    | succ fuel =>
      cases inner : (Source.evalE G F fuel left).run source with
      | mk result middle =>
        cases result with
        | error halt => rw [source_error G F fuel source middle conj left right halt inner] at run; cases run
        | ok value =>
          cases value with
          | val value =>
            obtain ⟨b,rfl⟩ := Source.Val.eq_bool value
            obtain ⟨a,native,post⟩ := l.success fuel source middle target b aligned inner
            rw [source_step G F fuel source middle conj b left right inner] at run
            by_cases take : needsRight conj b = true
            · simp only [if_pos take] at run
              obtain ⟨z,nativeRight,reached⟩ := r.success fuel middle after a.st choice post run
              refine ⟨⟨z.st,a.ext.trans z.ext⟩,?_,reached⟩
              rw [shortOperand_run,native]
              simp only [bind,Except.bind,if_pos take,nativeRight]
              rfl
            · simp only [if_neg take] at run
              have same : b = choice := Option.some.inj (congrArg
                (fun out : Source.R (Source.RVal E.layout .bool) =>
                  match out with | .ok (.val (.bool c)) => some c | _ => none) (congrArg Prod.fst run))
              have state : middle = after := congrArg Prod.snd run
              subst choice
              subst after
              refine ⟨a,?_,post⟩
              rw [shortOperand_run,native]
              simp only [bind,Except.bind,if_neg take]
              rfl
  · intro fuel source after target data aligned run
    cases fuel with
    | zero => cases run
    | succ fuel =>
      cases inner : (Source.evalE G F fuel left).run source with
      | mk result middle =>
        cases result with
        | error halt =>
          rw [source_error G F fuel source middle conj left right halt inner] at run
          have same : halt = .revert data := Except.error.inj (congrArg Prod.fst run)
          subst halt
          have native := l.revert fuel source middle target data aligned inner
          rw [shortOperand_run,native]
          rfl
        | ok value =>
          cases value with
          | val value =>
            obtain ⟨b,rfl⟩ := Source.Val.eq_bool value
            obtain ⟨a,native,post⟩ := l.success fuel source middle target b aligned inner
            rw [source_step G F fuel source middle conj b left right inner] at run
            by_cases take : needsRight conj b = true
            · simp only [if_pos take] at run
              have nativeRight := r.revert fuel middle after a.st data post run
              rw [shortOperand_run,native]
              simp only [bind,Except.bind,if_pos take,nativeRight]
            · simp only [if_neg take] at run
              cases run

#print axioms source_step
#print axioms source_error
#print axioms shortCondition

end Solidity.Lowering.G17
