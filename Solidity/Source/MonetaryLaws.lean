import Solidity.Source.Monetary

namespace Solidity.Source.Monetary
open Solidity.Roadmap (Word)

theorem credit_success_fits (balance : Balance) (value : Word) (result : Balance)
    (h : credit? balance value = some result) : Fits result := by
  unfold credit? at h
  split at h <;> simp_all only [Option.some.injEq, reduceCtorEq, Fits]

theorem debit_success_fits (balance : Balance) (value : Word) (result : Balance)
    (initial : Fits balance) (h : debit? balance value = some result) : Fits result := by
  unfold debit? at h
  split at h
  · cases Option.some.inj h
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) initial
  · cases h

theorem wide_zero_debit : debit? wide ⟨0, by decide⟩ = some wide := by decide

theorem debit_success_without_range :
    ∃ (balance : Balance) (value : Word) (result : Balance),
      debit? balance value = some result ∧ ¬ Fits result :=
  ⟨wide, ⟨0, by decide⟩, wide, wide_zero_debit, wide_not_fits⟩

end Solidity.Source.Monetary

/-- info: 'Solidity.Source.Monetary.credit_success_fits' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.credit_success_fits

/-- info: 'Solidity.Source.Monetary.debit_success_fits' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.debit_success_fits

/-- info: 'Solidity.Source.Monetary.wide_zero_debit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.wide_zero_debit

/-- info: 'Solidity.Source.Monetary.debit_success_without_range' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.debit_success_without_range
