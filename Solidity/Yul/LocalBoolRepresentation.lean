import Solidity.Yul.LocalBoolControl

/-! Proof-only exact-word relation for Boolean constructor differences.
Other local values and the complete Source world remain equal.
No runtime representation, readback policy or evaluator is changed. -/
namespace Solidity.Yul.LocalBoolRepresentation

def word {env : Solidity.Source.Env} (value : LocalValue env .bool) : Word :=
  LocalOperations.scalarWord value (LocalOperations.boolShape env)

inductive Value (env : Solidity.Source.Env) :
    {ty : Solidity.Source.STy} → LocalValue env ty → LocalValue env ty → Prop where
  | same {ty : Solidity.Source.STy} (value : LocalValue env ty) : Value env value value
  | boolean {one two : LocalValue env .bool} :
      word one = word two → Value env one two

inductive Locals (env : Solidity.Source.Env) :
    {ctx : Solidity.Source.RCtx} → LocalValues env ctx → LocalValues env ctx → Prop where
  | same {ctx : Solidity.Source.RCtx} (values : LocalValues env ctx) : Locals env values values
  | cons {ty : Solidity.Source.STy} {ctx : Solidity.Source.RCtx}
      {one two : LocalValue env ty} {left right : LocalValues env ctx} :
      Value env one two → Locals env left right →
      Locals env (ctx := ty :: ctx) (one,left) (two,right)

inductive Outcome (env : Solidity.Source.Env) :
    Solidity.Source.R (LocalValue env .bool) →
    Solidity.Source.R (LocalValue env .bool) → Prop where
  | same (value : Solidity.Source.R (LocalValue env .bool)) : Outcome env value value
  | boolean {one two : LocalValue env .bool} :
      word one = word two → Outcome env (.ok one) (.ok two)

def State {env : Solidity.Source.Env} {ctx : Solidity.Source.RCtx}
    (one two : LocalState env ctx) : Prop :=
  Locals env one.1 two.1 ∧ one.2 = two.2

def Run {env : Solidity.Source.Env} {ctx : Solidity.Source.RCtx}
    (one two : Solidity.Source.R (LocalValue env .bool) × LocalState env ctx) : Prop :=
  Outcome env one.1 two.1 ∧ State one.2 two.2

theorem value_word : ∀ (env : Solidity.Source.Env) (one two : Solidity.Yul.LocalValue env .bool),
 Solidity.Yul.LocalBoolRepresentation.Value env one two →
 Solidity.Yul.LocalBoolRepresentation.word one = Solidity.Yul.LocalBoolRepresentation.word two := by

  intro env one two related
  cases related with
  | same value => rfl
  | boolean same => exact same

theorem not_congr : ∀ (env : Solidity.Source.Env) (one two : Solidity.Yul.LocalValue env .bool),
 Solidity.Yul.LocalBoolRepresentation.word one = Solidity.Yul.LocalBoolRepresentation.word two →
 Solidity.Yul.LocalOperations.boolNot one = Solidity.Yul.LocalOperations.boolNot two := by

  intro env one two same
  change Solidity.Yul.LocalOperations.scalarWord one (Solidity.Yul.LocalOperations.boolShape env) =
   Solidity.Yul.LocalOperations.scalarWord two (Solidity.Yul.LocalOperations.boolShape env) at same
  unfold Solidity.Yul.LocalOperations.boolNot Solidity.Yul.LocalOperations.boolInput
  rw [same]

theorem read : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (one two : Solidity.Yul.LocalValues env ctx),
 Solidity.Yul.LocalBoolRepresentation.Locals env one two →
 ∀ (ty : Solidity.Source.STy) (index : Solidity.Source.Idx ctx ty),
 Solidity.Yul.LocalBoolRepresentation.Value env (one.get index) (two.get index) := by

  intro env ctx one two related
  induction related with
  | same values =>
    intro ty index
    exact Solidity.Yul.LocalBoolRepresentation.Value.same _
  | cons head tail ih =>
    intro ty index
    cases index with
    | here => exact head
    | there index => exact ih _ index

theorem write : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx) (ty : Solidity.Source.STy)
 (index : Solidity.Source.Idx ctx ty) (one two : Solidity.Yul.LocalValues env ctx)
 (left right : Solidity.Yul.LocalValue env ty),
 Solidity.Yul.LocalBoolRepresentation.Locals env one two →
 Solidity.Yul.LocalBoolRepresentation.Value env left right →
 Solidity.Yul.LocalBoolRepresentation.Locals env (one.set index left) (two.set index right) := by

  intro env ctx ty index
  induction index with
  | here =>
    intro one two left right related values
    cases related with
    | same => exact Solidity.Yul.LocalBoolRepresentation.Locals.cons values (.same one.2)
    | cons head tail => exact Solidity.Yul.LocalBoolRepresentation.Locals.cons values tail
  | there index ih =>
    intro one two left right related values
    cases related with
    | same =>
      exact Solidity.Yul.LocalBoolRepresentation.Locals.cons (.same one.1) (ih one.2 one.2 left right (.same _) values)
    | cons head tail =>
      exact Solidity.Yul.LocalBoolRepresentation.Locals.cons head (ih _ _ left right tail values)

theorem observe : ∀ (env : Solidity.Source.Env) (one two : Solidity.Source.R (Solidity.Yul.LocalValue env .bool)),
 Solidity.Yul.LocalBoolRepresentation.Outcome env one two →
 one.map Solidity.Yul.LocalBoolRepresentation.word = two.map Solidity.Yul.LocalBoolRepresentation.word := by

  intro env one two related
  cases related with
  | same value => rfl
  | boolean same =>
    change Except.ok (Solidity.Yul.LocalBoolRepresentation.word _) = Except.ok (Solidity.Yul.LocalBoolRepresentation.word _)
    rw [same]

theorem truth_congr : ∀ (env : Solidity.Source.Env) (one two : Solidity.Yul.LocalValue env .bool),
 Solidity.Yul.LocalBoolRepresentation.word one = Solidity.Yul.LocalBoolRepresentation.word two →
 Solidity.Yul.LocalBoolControl.truth one = Solidity.Yul.LocalBoolControl.truth two := by

  intro env one two same
  exact congrArg (fun raw : Solidity.Yul.Word => raw.val != 0) same

theorem expression : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env ctx .bool)
 (proof : Solidity.Yul.LocalBoolExpr.Supported env ctx expr)
 (fuel : Nat) (one two : Solidity.Yul.LocalState env ctx),
 Solidity.Yul.LocalBoolRepresentation.State one two →
 Solidity.Yul.LocalBoolRepresentation.Run
   (Solidity.Yul.LocalBoolExpr.eval proof fuel one) (Solidity.Yul.LocalBoolExpr.eval proof fuel two) := by

  intro env ctx expr proof
  induction proof with
  | literal value =>
    intro fuel one two given
    cases fuel <;> exact ⟨.same _,given⟩
  | «local» index =>
    intro fuel one two given
    cases fuel with
    | zero => exact ⟨.same _,given⟩
    | succ fuel =>
      exact ⟨.boolean (Solidity.Yul.LocalBoolRepresentation.value_word env _ _
        (Solidity.Yul.LocalBoolRepresentation.read env ctx one.1 two.1 given.1 .bool index)),given⟩
  | not child ih =>
    intro fuel one two given
    cases fuel with
    | zero => exact ⟨.same _,given⟩
    | succ fuel =>
      have compared := ih fuel one two given
      cases leftActual : Solidity.Yul.LocalBoolExpr.eval child fuel one with
      | mk leftResult leftState =>
        cases rightActual : Solidity.Yul.LocalBoolExpr.eval child fuel two with
        | mk rightResult rightState =>
          rw [leftActual,rightActual] at compared
          rcases compared with ⟨outcomes,states⟩
          simp only [Solidity.Yul.LocalBoolExpr.not_step,leftActual,rightActual]
          change Solidity.Yul.LocalBoolRepresentation.Outcome env
            (leftResult.bind Solidity.Yul.LocalOperations.boolNot)
            (rightResult.bind Solidity.Yul.LocalOperations.boolNot) ∧
            Solidity.Yul.LocalBoolRepresentation.State leftState rightState
          cases outcomes with
          | same => exact ⟨.same _,states⟩
          | @boolean left right words =>
            change Solidity.Yul.LocalBoolRepresentation.Outcome env
              (Solidity.Yul.LocalOperations.boolNot left) (Solidity.Yul.LocalOperations.boolNot right) ∧ _
            rw [Solidity.Yul.LocalBoolRepresentation.not_congr env left right words]
            exact ⟨.same _,states⟩
  | assign index child ih =>
    intro fuel one two given
    cases fuel with
    | zero => exact ⟨.same _,given⟩
    | succ fuel =>
      have compared := ih fuel one two given
      cases leftActual : Solidity.Yul.LocalBoolExpr.eval child fuel one with
      | mk leftResult leftState =>
        cases rightActual : Solidity.Yul.LocalBoolExpr.eval child fuel two with
        | mk rightResult rightState =>
          rw [leftActual,rightActual] at compared
          rcases compared with ⟨outcomes,states⟩
          simp only [Solidity.Yul.LocalBoolExpr.assign_step,leftActual,rightActual]
          cases outcomes with
          | same =>
            cases leftResult with
            | error halt => exact ⟨.same _,states⟩
            | ok value =>
              exact ⟨.same _,⟨Solidity.Yul.LocalBoolRepresentation.write env ctx .bool index
                leftState.1 rightState.1 value value states.1 (.same _),states.2⟩⟩
          | @boolean left right words =>
            exact ⟨.boolean words,⟨Solidity.Yul.LocalBoolRepresentation.write env ctx .bool index
              leftState.1 rightState.1 left right states.1 (.boolean words),states.2⟩⟩

theorem outcome_cases : ∀ (env : Solidity.Source.Env)
 (one two : Solidity.Source.R (Solidity.Yul.LocalValue env .bool)),
 Solidity.Yul.LocalBoolRepresentation.Outcome env one two →
 (∃ halt, one = .error halt ∧ two = .error halt) ∨
 (∃ left right, one = .ok left ∧ two = .ok right ∧
   Solidity.Yul.LocalBoolRepresentation.word left = Solidity.Yul.LocalBoolRepresentation.word right) := by

  intro env one two related
  cases related with
  | same =>
    cases one with
    | error halt => exact Or.inl ⟨halt,rfl,rfl⟩
    | ok value => exact Or.inr ⟨value,value,rfl,rfl,rfl⟩
  | @boolean left right words =>
    exact Or.inr ⟨left,right,rfl,rfl,words⟩

end Solidity.Yul.LocalBoolRepresentation
