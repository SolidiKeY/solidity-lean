import Solidity.Yul.RawCheckedIfElse
import Solidity.Yul.RawCheckedSequenceHorizon
import Solidity.Yul.RawLoopBodyHorizon

/-! Exact full-frame stability for completed mixed if/else execution.
Timeout prefixes are excluded, and Source transport retains its checked/coherent premises. -/
namespace Solidity.Yul.RawCheckedIfElseHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (yes no : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (one : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control yes)
 (two : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control no)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedIfElse.run test one two pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedIfElse.run test one two pipeline (fuel+1) state =
 Solidity.Yul.RawCheckedIfElse.run test one two pipeline fuel state := by
  intro ctx returns modifier control condition yes no test one two pipeline fuel state terminal
  cases fuel with
  | zero => exact False.elim (terminal rfl)
  | succ fuel =>
    cases first : RawCondition.eval test fuel state with
    | mk result next =>
      cases result with
      | error halt =>
        have ready : (RawCondition.eval test fuel state).1 ≠ .error .timeout := by
          rw [first]
          intro bad
          have haltEq : halt = Solidity.Source.Halt.timeout := Except.error.inj bad
          subst halt
          exact terminal (by simp only [RawCheckedIfElse.run,first])
        have stable := RawLoopBodyHorizon.conditionSuccessor ctx condition test fuel state ready
        simp only [RawCheckedIfElse.run,stable,first]
      | ok choice =>
        have ready : (RawCondition.eval test fuel state).1 ≠ .error .timeout := by
          rw [first]
          intro bad
          cases bad
        have stable := RawLoopBodyHorizon.conditionSuccessor ctx condition test fuel state ready
        cases choice with
        | false =>
          have bodyReady : (RawCheckedSequence.block two pipeline fuel next).1 ≠ .error .timeout := by
            simpa only [RawCheckedIfElse.run,first,Bool.false_eq_true,if_false] using terminal
          have bodyStable := RawCheckedSequenceHorizon.blockExtension ctx returns modifier control no two pipeline fuel 1 next bodyReady
          simp only [RawCheckedIfElse.run,stable,first,Bool.false_eq_true,if_false,bodyStable]
        | true =>
          have bodyReady : (RawCheckedSequence.block one pipeline fuel next).1 ≠ .error .timeout := by
            simpa only [RawCheckedIfElse.run,first,if_true] using terminal
          have bodyStable := RawCheckedSequenceHorizon.blockExtension ctx returns modifier control yes one pipeline fuel 1 next bodyReady
          simp only [RawCheckedIfElse.run,stable,first,if_true,bodyStable]

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (yes no : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (one : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control yes)
 (two : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control no)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedIfElse.run test one two pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedIfElse.run test one two pipeline (fuel+extra) state =
 Solidity.Yul.RawCheckedIfElse.run test one two pipeline fuel state := by
  intro ctx returns modifier control condition yes no test one two pipeline fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (RawCheckedIfElse.run test one two pipeline (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (successor ctx returns modifier control condition yes no test one two pipeline (fuel+extra) state ready).trans ih

theorem sourceExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (yes no : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (one : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control yes)
 (two : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control no)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel extra nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Yul.RawCheckedIfElse.run test one two glob.pipeline fuel state).1 ≠ .error .timeout →
 (Solidity.Source.execS glob frame (fuel+extra) nps ph
   (Solidity.Source.RStmt.ifElse condition (.block yes) (.block no)) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.ifElse condition (.block yes) (.block no)) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) := by
  intro ctx returns modifier control condition yes no test one two glob frame checked fuel extra nps ph state same terminal
  have first := RawCheckedIfElse.correct test one two glob frame checked fuel nps ph state same
  have later := RawCheckedIfElse.correct test one two glob frame checked (fuel+extra) nps ph state same
  rw [extension ctx returns modifier control condition yes no test one two glob.pipeline fuel extra state terminal] at later
  exact later.2.trans first.2.symm

end Solidity.Yul.RawCheckedIfElseHorizon
