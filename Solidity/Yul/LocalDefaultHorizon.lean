import Solidity.Yul.LocalDefaultItems
import Solidity.Yul.LocalItemHorizon

/-! Completed-run fuel stability for existing heterogeneous default items and blocks.
Raw surviving locals and exact context restoration are preserved. -/
namespace Solidity.Yul.LocalDefaultHorizon

theorem successor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types) (final : Solidity.Yul.LocalState env out),
 Solidity.Yul.LocalDefaultItems.run proof fuel state = .normal final →
 Solidity.Yul.LocalDefaultItems.run proof (fuel+1) state = .normal final := by
  intro env returns modifier control types out items proof
  induction proof with
  | body child =>
    exact Solidity.Yul.LocalItemHorizon.successor env returns modifier control _ _ _ child
  | declaration value tail ih =>
    intro fuel state final completed
    cases fuel with
    | zero => cases completed
    | succ fuel =>
      cases fuel with
      | zero => cases completed
      | succ fuel =>
        cases fuel with
        | zero => cases completed
        | succ fuel =>
          exact ih (fuel+2) ((.clean value.value,state.1),state.2) final completed


theorem extension : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items)
 (fuel extra : Nat) (state : Solidity.Yul.LocalState env types) (final : Solidity.Yul.LocalState env out),
 Solidity.Yul.LocalDefaultItems.run proof fuel state = .normal final →
 Solidity.Yul.LocalDefaultItems.run proof (fuel+extra) state = .normal final := by
  intro env returns modifier control types out items proof fuel extra state final completed
  induction extra with
  | zero => exact completed
  | succ extra ih =>
    exact Solidity.Yul.LocalDefaultHorizon.successor env returns modifier control types out items proof (fuel+extra) state final ih

theorem blockSuccessor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types) (final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultItems.blockRun proof fuel state = .normal final →
 Solidity.Yul.LocalDefaultItems.blockRun proof (fuel+1) state = .normal final := by
  intro env returns modifier control types out items proof fuel state final completed
  cases fuel with
  | zero => cases completed
  | succ fuel =>
    cases actual : Solidity.Yul.LocalDefaultItems.run proof fuel state with
    | normal middle =>
      have same := Solidity.Yul.LocalDefaultHorizon.successor env returns modifier control types out items proof fuel state middle actual
      simpa only [Solidity.Yul.LocalDefaultItems.blockRun,same,actual] using completed
    | halted halt middle =>
      simp only [Solidity.Yul.LocalDefaultItems.blockRun,actual,Solidity.Yul.LocalDefaultItems.close] at completed
      cases completed

theorem blockExtension : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (types out : Solidity.Source.RCtx)
 (items : Solidity.Source.RItems env returns modifier control types out)
 (proof : Solidity.Yul.LocalDefaultItems.Supported env returns modifier control items)
 (fuel extra : Nat) (state : Solidity.Yul.LocalState env types) (final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultItems.blockRun proof fuel state = .normal final →
 Solidity.Yul.LocalDefaultItems.blockRun proof (fuel+extra) state = .normal final := by
  intro env returns modifier control types out items proof fuel extra state final completed
  induction extra with
  | zero => exact completed
  | succ extra ih =>
    exact Solidity.Yul.LocalDefaultHorizon.blockSuccessor env returns modifier control types out items proof (fuel+extra) state final ih

end Solidity.Yul.LocalDefaultHorizon
