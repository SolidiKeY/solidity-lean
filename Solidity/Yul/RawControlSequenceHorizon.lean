import Solidity.Yul.RawControlSequence
import Solidity.Yul.RawLoopBodyHorizon

/-! Concrete control-sequence/block horizons preserve exact flows and whole raw frames.
Only a normal head executes the tail; break/continue/error short-circuit unchanged. -/
namespace Solidity.Yul.RawControlSequenceHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawControlSequence.run proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawControlSequence.run proof (fuel+1) state = Solidity.Yul.RawControlSequence.run proof fuel state := by
  intro ctx returns modifier u items proof
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
      have ready : (Solidity.Yul.RawLoopBody.run head fuel state).1 ≠ .error .timeout := by
        intro bad
        apply terminal
        rw [Solidity.Yul.RawControlSequence.run_cons]
        dsimp only
        rw [bad]
      have same := Solidity.Yul.RawLoopBodyHorizon.successor ctx returns modifier u _ head fuel state ready
      rw [Solidity.Yul.RawControlSequence.run_cons,Solidity.Yul.RawControlSequence.run_cons,same]
      cases actual : Solidity.Yul.RawLoopBody.run head fuel state with
      | mk result next =>
        cases result with
        | error halt => rfl
        | ok flow =>
          cases flow with
          | normal =>
            apply ih fuel next
            rw [Solidity.Yul.RawControlSequence.run_cons,actual] at terminal
            exact terminal
          | break_ h => rfl
          | continue_ h => rfl
          | leave_ impossible => cases impossible

theorem blockSuccessor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawControlSequence.block proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawControlSequence.block proof (fuel+1) state = Solidity.Yul.RawControlSequence.block proof fuel state := by
  intro ctx returns modifier u items proof fuel state terminal
  cases fuel with
  | zero => exact False.elim (terminal rfl)
  | succ fuel =>
    exact Solidity.Yul.RawControlSequenceHorizon.successor ctx returns modifier u items proof fuel state terminal

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawControlSequence.run proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawControlSequence.run proof (fuel+extra) state = Solidity.Yul.RawControlSequence.run proof fuel state := by
  intro ctx returns modifier u items proof fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawControlSequence.run proof (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawControlSequenceHorizon.successor ctx returns modifier u items proof (fuel+extra) state ready).trans ih

theorem blockExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u items)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawControlSequence.block proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawControlSequence.block proof (fuel+extra) state = Solidity.Yul.RawControlSequence.block proof fuel state := by
  intro ctx returns modifier u items proof fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawControlSequence.block proof (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawControlSequenceHorizon.blockSuccessor ctx returns modifier u items proof (fuel+extra) state ready).trans ih

end Solidity.Yul.RawControlSequenceHorizon
