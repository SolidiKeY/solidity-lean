import Solidity.Source.MonetaryLaws

/-! H26 exact monetary helper laws over the immutable H19 interface.
No account, ledger, session, or reachability invariant is asserted here. -/
namespace Solidity.Source.Monetary
open Solidity.Roadmap (Word)

theorem credit_debit_roundtrip (b : Balance) (v : Word) (c : Balance)
    (h : credit? b v = some c) : debit? c v = some b := by
  unfold credit? at h
  split at h
  · cases Option.some.inj h
    simp only [debit?, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]
  · cases h

theorem debit_credit_roundtrip (b : Balance) (v : Word) (d : Balance)
    (hb : Fits b) (h : debit? b v = some d) : credit? d v = some b := by
  unfold debit? at h
  split at h
  · rename_i affordable
    cases Option.some.inj h
    simp only [credit?, Nat.sub_add_cancel affordable, show b < wordLimit from hb, ↓reduceIte]
  · cases h

theorem checkedWord_iff (b : Balance) (w : Word) :
    checkedWord b = some w ↔ Fits b ∧ w.val = b := by
  unfold checkedWord
  split
  · rename_i hb
    constructor
    · intro h
      cases Option.some.inj h
      exact ⟨hb, rfl⟩
    · intro h
      have hw : (⟨b, hb⟩ : Word) = w := Fin.ext h.2.symm
      exact congrArg some hw
  · rename_i hb
    constructor
    · intro h
      cases h
    · intro h
      exact False.elim (hb h.1)

/-- Backfill: exact affordability and result characterization. -/
theorem debit_eq_some_iff (b : Balance) (v : Word) (d : Balance) :
    debit? b v = some d ↔ v.val ≤ b ∧ d = b - v.val := by
  unfold debit?
  split <;> simp_all only [Option.some.injEq, reduceCtorEq, false_and,
    true_and, eq_comm]

/-- Backfill: exact refusal guard and result characterization. -/
theorem credit_eq_some_iff (b : Balance) (v : Word) (c : Balance) :
    credit? b v = some c ↔ Fits (b + v.val) ∧ c = b + v.val := by
  unfold credit?
  split <;> simp_all only [Fits, Option.some.injEq, reduceCtorEq,
    false_and, true_and, eq_comm]

/-- Backfill: the reverse round trip characterizes the missing range premise. -/
theorem reverse_roundtrip_iff (b : Balance) (v : Word) (d : Balance)
    (h : debit? b v = some d) : credit? d v = some b ↔ Fits b := by
  constructor
  · exact credit_success_fits d v b
  · intro hb
    exact debit_credit_roundtrip b v d hb h

end Solidity.Source.Monetary
