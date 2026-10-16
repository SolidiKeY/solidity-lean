import Solidity.TestSuite.ScopedProblems

/-! Native push suffix obligations from the pinned SolKey source.
Demanded primitive reads are eliminated before later writes duplicate them;
the signed three-push obligation closes within the unchanged closer bounds. -/

open Solidity
open scoped Scoped

/-- Appending then applying ADD/MUL updates the new primitive slot. -/
theorem Solkey.TestSuite.storagePushCompoundTarget.proved :
    ⊢ Solkey.TestSuite.storagePushCompoundTarget.problem := by
  sol_prove

/-- Nonzero DIV/MOD guards permit both appended zero values. -/
theorem Solkey.TestSuite.storagePushDivModTarget.proved :
    ⊢ Solkey.TestSuite.storagePushDivModTarget.problem := by
  sol_prove

/-- Discarded prefix and postfix increments both leave one. -/
theorem Solkey.TestSuite.storagePushIncrementTarget.proved :
    ⊢ Solkey.TestSuite.storagePushIncrementTarget.problem := by
  sol_prove

/-- Three signed pushes preserve the slot values -4, -1, -1 and length three. -/
theorem Solkey.TestSuite.storagePushCompoundSigned.proved :
    ⊢ Solkey.TestSuite.storagePushCompoundSigned.problem := by
  sol_prove (steps := 256)

/-- Storage-return receivers preserve default push, value push and pop order. -/
theorem Solkey.TestSuite.storagePushPopCallReceiver.proved :
    ⊢ Solkey.TestSuite.storagePushPopCallReceiver.problem := by
  sol_prove

