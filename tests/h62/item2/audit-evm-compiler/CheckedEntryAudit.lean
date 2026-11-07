import Solidity.Backend.Payments.EntrySuccess
import tests.h62.item2.«audit-evm-compiler».HeadlineAudit

/-! Actual checked-entry success for the existing nonempty storage-write fixture.
The observation and four excluded behaviors are unchanged. This is an intrinsic
model result, not Source adequacy or an external EVM gas/fork result. -/
namespace Solidity.H62.EvmCompilerAudit.CheckedEntry
open Evm Evm.Examples

def checkedCode : Option (List Instr) :=
  (Compiler.compile 0 (Frag.init []) setAge).map Compiler.Compilation.code

/-- The actual checked entry admits this program and executes its observed write. -/
theorem checked_entry_writes : WritesAge checkedCode := by
  unfold checkedCode
  rw [Compiler.compile_core_some admitted]
  exact compiled_setAge_writes

theorem reject_all_differs : checkedCode ≠ none := by
  intro h
  have observation : WritesAge checkedCode := checked_entry_writes
  rw [h] at observation
  exact reject_all_fails observation

theorem always_revert_differs : checkedCode ≠ some [.revert] := by
  intro h
  have observation : WritesAge checkedCode := checked_entry_writes
  rw [h] at observation
  exact always_revert_fails observation

theorem empty_code_differs : checkedCode ≠ some [] := by
  intro h
  have observation : WritesAge checkedCode := checked_entry_writes
  rw [h] at observation
  exact emit_nothing_fails observation

theorem pending_jump_differs : checkedCode ≠ some (compileProg 0 setAge ++ [.jump 1]) := by
  intro h
  have observation : WritesAge checkedCode := checked_entry_writes
  rw [h] at observation
  exact trailing_jump_fails observation

#print axioms checked_entry_writes
#print axioms reject_all_differs
#print axioms always_revert_differs
#print axioms empty_code_differs
#print axioms pending_jump_differs
end Solidity.H62.EvmCompilerAudit.CheckedEntry
