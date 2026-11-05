import Solidity.Backend.Executable.CreationReturnPartition
import Solidity.Backend.Executable.CreationPatchOrderControls

/-! Actual constructor return with all three byte classes and adjacent regions. -/
namespace Solidity.Backend.Executable.CreationReturnPartition.Controls
open Solidity.Backend Solidity.Backend.Creation
open CreationPatchOrder.Controls

theorem unchanged_byte : expected[0]? = artifact.runtime[0]? := by
  apply frame artifact links imms addresses compatible_tables expected constructor_returns 0
  · intro patch member
    simp only [imms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  · intro site member
    simp only [links,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide +kernel

theorem immutable_observed (j : Nat) (hj : j < 32) :
    expected[p.location.offset+j]? = p.value.toList[j]? :=
  immutable artifact links imms addresses compatible_tables expected constructor_returns
    p List.mem_cons_self j hj

/-- All certified positions are separated, including each side of the adjacent
immutable/library boundary. No constructor run is assumed for this geometry. -/
theorem no_cross_alias (j k : Nat) (hj : j < 32) (hk : k < 20) :
    p.location.offset+j ≠ s.location.offset+k :=
  cross_exclusive artifact links imms compatible_tables p List.mem_cons_self
    s List.mem_cons_self j k hj hk

/-- The complete explanation theorem selects the actual library region at its
first byte: compatibility rules out immutable ownership and the outside-region
certificate rules out the unchanged-input branch. -/
theorem classified_boundary : ∃ site ∈ links.sites, ∃ j, j < 20 ∧
    33 = site.location.offset+j ∧ expected[33]? = (addresses site.library).toList[j]? := by
  rcases partition artifact links imms addresses compatible_tables expected constructor_returns 33 with
    patched | linked | outside
  · obtain ⟨patch,member,j,hj,position,_⟩ := patched
    have different := cross_exclusive artifact links imms compatible_tables patch member
      s List.mem_cons_self j 0 hj (by decide +kernel)
    exact False.elim (different position.symm)
  · exact linked
  · have bound := outside.2.1 s List.mem_cons_self
    change 33 < 33 ∨ 33+20 ≤ 33 at bound
    omega

/-- Checks both ends of every nonempty region and the first absent return byte.
The argument bytes remain outside the returned runtime. -/
theorem boundaries :
    [expected[0]?,expected[1]?,expected[32]?,expected[33]?,expected[52]?,
      expected[53]?,expected[84]?,expected[85]?,expected[104]?,expected[105]?] =
    [some 0,some 17,some 17,some 51,some 51,some 34,some 34,some 68,some 68,none] := by
  first | rfl | decide +kernel | omega | simp only

theorem wrong_immutable : expected[1]? ≠ some 51 := by
  first | rfl | decide +kernel | omega | simp only

theorem no_argument_at_return_end : expected[105]? ≠ artifact.args[0]? := by
  first | rfl | decide +kernel | omega | simp only

end Solidity.Backend.Executable.CreationReturnPartition.Controls
