import Solidity.Yul.Views.StorageBalanceInputs
import Solidity.Yul.Views.DynamicSourceSequence
import Solidity.Yul.Views.SourceBalanceReads

namespace Solidity.Yul.Views

/-- All plans in this actual source sequence are validated storage operations.
The result includes the original owner's success/static-error behavior. -/
theorem runPackedSource_observed_balance {E Γ ps ts}
    (G : Source.Glob E) (F : Source.Fr)
    (plans : List (@PackedSlotPlan E.layout E.lay E.lay ps ts))
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) (b : Roadmap.Address) :
    sourceObservedBalance G (runPackedSource F plans s r).1.2 b = sourceObservedBalance G s b := by
  induction plans generalizing s r with
  | nil => rfl
  | cons p plans ih =>
    cases static : F.static
    · rw [runPackedSource,packedSourceStep_nonstatic F p s r static]
      have step := packedSourceStep_observed_balance G F p s r b
      rw [packedSourceStep_nonstatic F p s r static] at step
      exact (ih _ _).trans step
    · rw [runPackedSource_static F p plans s r static]

theorem runPackedSource_observed_funds {E Γ ps ts}
    (G : Source.Glob E) (F : Source.Fr)
    (plans : List (@PackedSlotPlan E.layout E.lay E.lay ps ts))
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :
    sourceObservedFunds G (runPackedSource F plans s r).1.2 = sourceObservedFunds G s := by
  funext address
  exact congrArg environmentWord (runPackedSource_observed_balance G F plans s r (sourceAddressOfEnvironment address))

theorem runPackedSource_locals {E Γ ps ts} (F : Source.Fr)
    (plans : List (@PackedSlotPlan E.layout E.lay E.lay ps ts))
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :
    (runPackedSource F plans s r).1.2.1=s.1 := by
  cases plans with
  | nil => rfl
  | cons p plans =>
    cases static : F.static
    · rw [runPackedSource_nonstatic F (p::plans) s r static]
    · rw [runPackedSource_static F p plans s r static]

/-- The actual balance expression AFTER the actual storage sequence observes
its original value, at the same n+2 horizon, and leaves the COMPLETE resulting
state unchanged. This does not erase the sequence's journal/storage changes.
This is a separate post-state observation, including on an error result; it
is NOT a claim that a monadic continuation runs after that error. -/
theorem runPackedSource_balanceLocal {E Γ ps ts}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (plans : List (@PackedSlotPlan E.layout E.lay E.lay ps ts))
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (index : Source.Idx Γ (.address false)) (b : Roadmap.Address)
    (localValue : s.1.get index=.address b) :
    (Source.evalE G F (n+2) (sourceBalanceExpr index)).run (runPackedSource F plans s r).1.2 =
      (.ok (.val (uintValueOfWord E.layout (sourceObservedBalance G s b))), (runPackedSource F plans s r).1.2) := by
  have found : (runPackedSource F plans s r).1.2.1.get index=.address b := by
    rw [runPackedSource_locals F plans s r]
    exact localValue
  rw [sourceBalanceLocal_run G F n _ index b found,runPackedSource_observed_balance]

end Solidity.Yul.Views
