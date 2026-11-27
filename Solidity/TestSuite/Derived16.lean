import Solidity.TestSuite.ScopedProblems


open Solidity
open scoped Scoped

theorem Solkey.TestSuite.storagePushCompoundTarget.proved :
    ⊢ Solkey.TestSuite.storagePushCompoundTarget.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushDivModTarget.proved :
    ⊢ Solkey.TestSuite.storagePushDivModTarget.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushIncrementTarget.proved :
    ⊢ Solkey.TestSuite.storagePushIncrementTarget.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushCompoundSigned.proved :
    ⊢ Solkey.TestSuite.storagePushCompoundSigned.problem := by
  sol_prove (steps := 256)

theorem Solkey.TestSuite.storagePushPopCallReceiver.proved :
    ⊢ Solkey.TestSuite.storagePushPopCallReceiver.problem := by
  sol_prove

