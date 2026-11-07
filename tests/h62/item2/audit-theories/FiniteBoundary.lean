import Solidity.Theory.Typed.Leaves

/-! A certificate for an intentionally empty simultaneous input telescope.
This preserves the frozen structural boundary; it does not manufacture a
witness or certify a compiler. -/
namespace H62.AuditTheories
open Solidity

/-- A finite storage shape cannot contain a direct path to a dynamic array. -/
theorem no_finite_array_path_input :
    ¬ ∃ (E T : Ty), T.Finite ∧ ∃ r : Path T (.ref (.array E)), r.direct = true := by
  rintro ⟨E, T, hT, r, hd⟩
  exact Ty.Finite.not_array hT r hd

#print axioms no_finite_array_path_input
end H62.AuditTheories
