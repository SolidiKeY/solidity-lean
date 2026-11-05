import Solidity.Yul.RawSequence
import Solidity.Yul.RawStatementHorizon

/-! Concrete same-context sequence/block completed horizons preserve the whole raw frame.
Only actual certificates and original non-timeout execution are required. -/
namespace Solidity.Yul.RawSequenceHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawSequence.Supported ctx returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSequence.run proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSequence.run proof (fuel+1) state = Solidity.Yul.RawSequence.run proof fuel state := by
  intro ctx returns modifier control items proof
  induction proof with
  | nil =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel => rfl
  | cons head tail ih =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      have ready : (Solidity.Yul.RawCoherent.execS head fuel state).1 ≠ .error .timeout := by
        intro bad
        apply terminal
        rw [Solidity.Yul.RawSequence.run_cons]
        dsimp only
        rw [bad]
      have same := Solidity.Yul.RawStatementHorizon.coherentSuccessor ctx returns modifier control _ head fuel state ready
      rw [Solidity.Yul.RawSequence.run_cons,Solidity.Yul.RawSequence.run_cons,same]
      cases actual : Solidity.Yul.RawCoherent.execS head fuel state with
      | mk result next =>
        cases result with
        | error halt => rfl
        | ok value =>
          apply ih fuel next
          rw [Solidity.Yul.RawSequence.run_cons,actual] at terminal
          exact terminal

theorem blockSuccessor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawSequence.Supported ctx returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSequence.block proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSequence.block proof (fuel+1) state = Solidity.Yul.RawSequence.block proof fuel state := by
  intro ctx returns modifier control items proof fuel state terminal
  cases fuel with
  | zero => exact False.elim (terminal rfl)
  | succ fuel =>
    exact Solidity.Yul.RawSequenceHorizon.successor ctx returns modifier control items proof fuel state terminal

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawSequence.Supported ctx returns modifier control items)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSequence.run proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSequence.run proof (fuel+extra) state = Solidity.Yul.RawSequence.run proof fuel state := by
  intro ctx returns modifier control items proof fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawSequence.run proof (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawSequenceHorizon.successor ctx returns modifier control items proof (fuel+extra) state ready).trans ih

theorem blockExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawSequence.Supported ctx returns modifier control items)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSequence.block proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSequence.block proof (fuel+extra) state = Solidity.Yul.RawSequence.block proof fuel state := by
  intro ctx returns modifier control items proof fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawSequence.block proof (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawSequenceHorizon.blockSuccessor ctx returns modifier control items proof (fuel+extra) state ready).trans ih

end Solidity.Yul.RawSequenceHorizon
