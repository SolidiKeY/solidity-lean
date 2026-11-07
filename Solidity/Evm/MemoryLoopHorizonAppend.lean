import Solidity.Evm.MemoryLoopFiniteHorizon

/-! Exact concatenation of the existing source and target finite iterators at
an actual pending observation. Resuming the reached state equals the full summed
horizon, including a zero remainder. No state reset, extra fuel convention,
termination or source/target correspondence is assumed. -/
namespace Solidity.Evm.Memory

theorem iterN_add_of_pending {α : Type} {body : α → TRes α} {condition : α → TRes Bool}
    {elapsed : Nat} {initial reached : α}
    (pending : TLoop.iterN body condition elapsed initial=.inl reached) (remaining : Nat) :
    TLoop.iterN body condition (elapsed+remaining) initial=TLoop.iterN body condition remaining reached := by
  induction elapsed generalizing initial with
  | zero => cases pending; simp only [Nat.zero_add]
  | succ elapsed ih =>
    simp only [TLoop.iterN] at pending
    cases turn : TLoop.step body condition initial with
    | inl next =>
      rw [turn] at pending
      have resumed := ih pending
      simpa only [Nat.succ_add,TLoop.iterN,turn] using resumed
    | inr result =>
      rw [turn] at pending
      cases pending

theorem loopIterN_add_of_pending {condition body : Machine → Out} {elapsed : Nat} {initial reached : Machine}
    (pending : loopIterN condition body elapsed initial=.inl reached) (remaining : Nat) :
    loopIterN condition body (elapsed+remaining) initial=loopIterN condition body remaining reached := by
  induction elapsed generalizing initial with
  | zero => cases pending; simp only [Nat.zero_add]
  | succ elapsed ih =>
    simp only [loopIterN] at pending
    cases turn : loopTurn condition body initial with
    | inl next =>
      rw [turn] at pending
      have resumed := ih pending
      simpa only [Nat.succ_add,loopIterN,turn] using resumed
    | inr result =>
      rw [turn] at pending
      cases pending

end Solidity.Evm.Memory
