import Solidity.Yul.RawLoopBody
import Solidity.Yul.LocalItemFailure

/-! Error classification ONLY for actual raw Boolean-certificate conditions,
expression statements, same-context sequences/blocks and loop bodies.
Break/continue successes are retained. No general Yul or initialized-loop error
classification, Source dirty-readback or admission claim is made. -/
namespace Solidity.Yul.RawBoolFailure

theorem condition : ∀ (ctx : Solidity.Source.Ctx)
 (expr : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys expr)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx) (halt : Solidity.Source.Halt),
 (Solidity.Yul.RawCondition.eval proof fuel state).1 = .error halt → halt = .timeout := by
  intro ctx expr proof fuel state halt failed
  unfold Solidity.Yul.RawCondition.eval at failed
  cases actual : Solidity.Yul.LocalBoolControl.eval proof fuel (Solidity.Yul.RawCoherent.prepare state) with
  | mk tag next =>
    rw [actual] at failed
    cases tag with
    | error error =>
      have same := Solidity.Yul.LocalBoolFailure.control ctx.env ctx.tys expr proof fuel
        (Solidity.Yul.RawCoherent.prepare state) error (congrArg Prod.fst actual)
      cases failed
      exact same
    | ok value => cases failed

theorem statement : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawSource.Supported ctx returns modifier control stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx) (halt : Solidity.Source.Halt),
 (Solidity.Yul.RawCoherent.execS proof fuel state).1 = .error halt → halt = .timeout := by
  intro ctx returns modifier control stmt proof
  cases proof with
  | expression inside =>
    intro fuel state halt failed
    exact Solidity.Yul.LocalItemFailure.statement ctx.env ctx.tys _ inside fuel
      (Solidity.Yul.RawCoherent.prepare state) halt failed

theorem sequence : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawSequence.Supported ctx returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx) (halt : Solidity.Source.Halt),
 (Solidity.Yul.RawSequence.run proof fuel state).1 = .error halt → halt = .timeout := by
  intro ctx returns modifier control items proof
  induction proof with
  | nil =>
    intro fuel state halt failed
    cases fuel <;> cases failed <;> rfl
  | cons head tail ih =>
    intro fuel state halt failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      rw [Solidity.Yul.RawSequence.run_cons] at failed
      cases actual : Solidity.Yul.RawCoherent.execS head fuel state with
      | mk tag next =>
        rw [actual] at failed
        cases tag with
        | error error =>
          have same := statement ctx returns modifier control _ head fuel state error (congrArg Prod.fst actual)
          cases failed
          exact same
        | ok value => exact ih fuel next halt failed

theorem block : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawSequence.Supported ctx returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx) (halt : Solidity.Source.Halt),
 (Solidity.Yul.RawSequence.block proof fuel state).1 = .error halt → halt = .timeout := by
  intro ctx returns modifier control items proof fuel state halt failed
  cases fuel with
  | zero => cases failed; rfl
  | succ fuel => exact sequence ctx returns modifier control items proof fuel state halt failed

theorem body : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx) (halt : Solidity.Source.Halt),
 (Solidity.Yul.RawLoopBody.run proof fuel state).1 = .error halt → halt = .timeout := by
  intro ctx returns modifier u stmt proof
  induction proof with
  | plain inside =>
    intro fuel state halt failed
    change (Solidity.Yul.RawSequence.block inside fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)) = .error halt at failed
    cases actual : Solidity.Yul.RawSequence.block inside fuel state with
    | mk tag next =>
      rw [actual] at failed
      cases tag with
      | error error =>
        have same := block ctx returns modifier ⟨true,u⟩ _ inside fuel state error (congrArg Prod.fst actual)
        cases failed
        exact same
      | ok value => cases failed
  | skip | break_ | continue_ =>
    intro fuel state halt failed
    cases fuel <;> cases failed <;> rfl
  | ifThen test inside ih =>
    intro fuel state halt failed
    cases fuel with
    | zero => cases failed; rfl
    | succ fuel =>
      rw [Solidity.Yul.RawLoopBody.run_ifThen] at failed
      cases actual : Solidity.Yul.RawCondition.eval test fuel state with
      | mk tag next =>
        rw [actual] at failed
        cases tag with
        | error error =>
          have same := condition ctx _ test fuel state error (congrArg Prod.fst actual)
          cases failed
          exact same
        | ok choice =>
          cases choice with
          | false => cases failed
          | true => exact ih fuel next halt failed

end Solidity.Yul.RawBoolFailure
