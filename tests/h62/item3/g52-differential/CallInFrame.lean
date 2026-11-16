import Solidity.Evm.MachineV2

/-! Guarded regression: CALLIN frame and foreign-account balances must not be
inferred from its return-buffer agreement alone. This general core law includes
insufficient funds, rejection, self-call and accepted payment. It strengthens
the memory/storage projection in the existing readonly-calls ExecutionReplies
controls without importing those controls or changing either machine.

This concerns callInStep after its input bytes have been supplied. It does not
cover readBytes failure, emitted Site origin, reference CALL, callee execution,
depth, gas, an approved native domain or any full H68 certificate. -/
namespace Solidity.Evm

/-- Restoring the two mutable base fields recovers the entire caller frame;
only the caller and callee can have changed balances. No successful-call,
acceptance, distinct-callee or sufficient-funds premise is required. -/
theorem callInStep_frame (m : MachineV2) (v a : Fin W)
    (input : List UInt8) (st : List Word) :
    ∃ next, callInStep m v a input st = .ok next 0 ∧
      {next.base with stack := m.base.stack, bal := m.base.bal} = m.base ∧
      ∀ account, account ≠ m.base.self → account ≠ a →
        next.base.bal account = m.base.bal account := by
  simp only [callInStep]
  by_cases funds : m.base.bal m.base.self < v.val
  · rw [if_pos funds]
    exact ⟨_, rfl, rfl, fun _ _ _ => rfl⟩
  · rw [if_neg funds]
    by_cases rejected : m.base.accepts a v = false
    · rw [if_pos rejected]
      exact ⟨_, rfl, rfl, fun _ _ _ => rfl⟩
    · rw [if_neg rejected]
      by_cases self : a = m.base.self
      · rw [if_pos self]
        exact ⟨_, rfl, rfl, fun _ _ _ => rfl⟩
      · rw [if_neg self]
        refine ⟨_, rfl, rfl, ?_⟩
        intro account otherSelf otherCallee
        change pay m.base.bal m.base.self a v.val account = m.base.bal account
        simp only [pay, upd, if_neg otherCallee, if_neg otherSelf]

#print axioms callInStep_frame
end Solidity.Evm
