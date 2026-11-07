import Solidity.Frontend.NumericLiteralProofs.Refusals
import Solidity.Frontend.NumericLiteralProofs.WordTable

/-! # Accepted-token, source-range and separation consequences -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem solWord_no_num (raw : Bytes) (n : NumLit) : solWord raw ≠ some (.num n) := by
  intro h
  unfold solWord at h
  split at h
  · next t ht =>
      cases h
      exact solWordTable_no_num raw n ht
  · cases h
  · split at h <;> cases h

theorem solTok_numeric {raw : Bytes} {n : NumLit} (h : solTok raw = some (.num n)) :
    Hexadecimal raw n ∨ Decimal raw n := by
  unfold solTok at h
  split at h
  · exact False.elim (solWord_no_num raw n h)
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · split at h
          · obtain ⟨_, _, hh⟩ := Option.map_eq_some_iff.mp h
            cases hh
          · cases h
        · split at h
          · split at h
            · cases h
            · obtain ⟨_, _, hh⟩ := Option.map_eq_some_iff.mp h
              cases hh
          · cases h
        · split at h
          · next hn =>
              cases h
              exact Or.inl (Hexadecimal.complete hn)
          · obtain ⟨_, hd, hh⟩ := Option.map_eq_some_iff.mp h
            cases hh
            exact Or.inr (Decimal.complete hd)

/-- Accepted Solidity-mode numeric tokens carry an exact spelling derivation. -/
theorem classify_numeric {raw : Bytes} {n : NumLit}
    (h : classify .sol raw = some (.tok (.num n))) :
    Hexadecimal raw n ∨ Decimal raw n := by
  unfold classify at h
  split at h
  · cases h
  · obtain ⟨_, ht, hh⟩ := Option.map_eq_some_iff.mp h
    cases hh
    exact solTok_numeric ht

end Solidity.Frontend.NumericLiteralProofs
