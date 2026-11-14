import Solidity.Backend.StructuredFlow.ExitSelector
import Solidity.Backend.StructuredFlow.BranchControls

/-! Inhabited full-machine relative-exit controls and actual off-by-one refusal. -/
namespace Solidity.Backend.StructuredFlow.ExitControls
open Solidity.Evm
open Solidity.Backend.StructuredFlow.BranchControls

theorem skips_revert_and_fault :
    run (Exit.emit 3 ++ ([.revert,.pop,.pop] ++ write ⟨7,by decide⟩)) initial =
      .ok (stored ⟨7,by decide⟩) 0 := by
  exact (Exit.skips [.revert,.pop,.pop] (write ⟨7,by decide⟩) initial).trans (by rfl)

theorem skipped_write_is_inert :
    run (Exit.emit (write ⟨3,by decide⟩).length ++
      (write ⟨3,by decide⟩ ++ write ⟨7,by decide⟩)) initial =
      .ok (stored ⟨7,by decide⟩) 0 := by
  rw [Exit.skips]
  rfl

/-- Isolate fault suppression: the second pop faults if these instructions run. -/
theorem skips_fault :
    run (Exit.emit 2 ++ ([.pop,.pop] ++ write ⟨7,by decide⟩)) initial =
      .ok (stored ⟨7,by decide⟩) 0 := by
  exact (Exit.skips [.pop,.pop] (write ⟨7,by decide⟩) initial).trans (by rfl)

/-- The continuation does not overwrite the skipped store's distinct address. -/
theorem skipped_distinct_cell_is_inert :
    run (Exit.emit 2 ++ ([.push w[3],.mstore 6] ++ write ⟨7,by decide⟩)) initial =
      .ok (stored ⟨7,by decide⟩) 0 := by
  exact (Exit.skips [.push w[3],.mstore 6] (write ⟨7,by decide⟩) initial).trans (by rfl)

theorem branch_exit :
    run ((Branch.emit (condition true) (Exit.emit 3) [.revert] ++ [.revert]) ++
      write ⟨7,by decide⟩) initial = .ok (stored ⟨7,by decide⟩) 0 := by
  exact (Exit.branch_left (condition := condition true) (right := [.revert])
    (skipped := [.revert]) (continuation := write ⟨7,by decide⟩) (post := initial) rfl).trans (by rfl)

theorem condition_effect :
    run ((Branch.emit [.push w[11],.mstore 6,.push w[1]] (Exit.emit 3) [.revert] ++
      [.revert]) ++ write ⟨7,by decide⟩) initial =
      .ok {initial with mem := upd (upd initial.mem 6 w[11]) 5 w[7]} 0 := by
  exact (Exit.branch_left (condition := [.push w[11],.mstore 6,.push w[1]])
    (right := [.revert]) (skipped := [.revert]) (continuation := write ⟨7,by decide⟩)
    (post := {initial with mem := upd initial.mem 6 w[11]}) rfl).trans (by rfl)

/-- Missing the compiler's one jump instruction executes the caller's revert. -/
theorem missing_jump_refused :
    run ((Branch.emit (condition true) (Exit.emit 2) [.revert] ++ [.revert]) ++
      write ⟨7,by decide⟩) initial = .revert := by
  rfl

theorem false_reaches_else :
    run ((Branch.emit (condition false) (Exit.emit 3) [.revert] ++ [.revert]) ++
      write ⟨7,by decide⟩) initial = .revert := by
  rfl

/-- Caller tail, allocator, aliases and sentinel survive the reached write. -/
theorem frame_fields :
    (stored ⟨7,by decide⟩).stack = [w[77]] ∧
    (stored ⟨7,by decide⟩).mem 0 = w[132] ∧
    (stored ⟨7,by decide⟩).mem 1 = w[128] ∧
    (stored ⟨7,by decide⟩).mem 2 = w[128] ∧
    (stored ⟨7,by decide⟩).mem 9 = w[99] := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩
end Solidity.Backend.StructuredFlow.ExitControls
