import Solidity.TestSuite.CoreProblems
import Solidity.Calculus.Core.ProvesDerive
import Solidity.Calculus.Core.Surface

/-!
# solkey's `TestSuite`, `⊢` scoped: the box obligations

Under `open scoped Solidity.Core.Surface` an obligation is stated `⊢ φ`,
the scoped sequent (`Core.Proves`), and `sol_prove` proves it by the walk of
`Calculus/Core/ProvesDerive.lean`: the `Derived` modules' text, the
statement scoped (`CoreProblems.lean`).  These are Derived1's and Derived9's
box obligations, the three whose closer leaves goals (each closed by the
same leaf tactics), and `testStorageNestedPushReturnAlias`, where the walk
leaves one goal of today's calculus and `Derived7` two (`docs/intrinsic.md`,
W3 lane `testsuite`).  The flip of the `Derived` modules waits on the
diamond: `Proves.close` takes no leaf behind a diamond update, and 330 of
the 437 obligations are diamonds.
-/

open Solidity Proves
open scoped Solidity.Core.Surface

theorem Solkey.TestSuite.additionStorageWrite.proved_seq : ⊢ Solkey.TestSuite.additionStorageWrite.problem.core := by
  sol_prove

theorem Solkey.TestSuite.storageIndexAddAssign.proved_seq : ⊢ Solkey.TestSuite.storageIndexAddAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.storageIndexArrayAddAssignOutOfBoundsReverts.proved_seq : ⊢ Solkey.TestSuite.storageIndexArrayAddAssignOutOfBoundsReverts.problem.core := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexArrayReadOutOfBoundsReverts.proved_seq : ⊢ Solkey.TestSuite.storageIndexArrayReadOutOfBoundsReverts.problem.core := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexReadComplexReceiverBindLocalRoot.proved_seq : ⊢ Solkey.TestSuite.storageIndexReadComplexReceiverBindLocalRoot.problem.core := by
  sol_prove

theorem Solkey.TestSuite.requireFalseLiteral.proved_seq : ⊢ Solkey.TestSuite.requireFalseLiteral.problem.core := by
  sol_prove

theorem Solkey.TestSuite.storageBoolArrayRead.proved_seq : ⊢ Solkey.TestSuite.storageBoolArrayRead.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexWriteNse.proved_seq : ⊢ Solkey.TestSuite.memoryIndexWriteNse.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryToStorageIndexArrayCopyRootOutOfBoundsReverts.proved_seq : ⊢ Solkey.TestSuite.memoryToStorageIndexArrayCopyRootOutOfBoundsReverts.problem.core := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.testStorageNestedPushReturnAlias.proved_seq : ⊢ Solkey.TestSuite.testStorageNestedPushReturnAlias.problem.core := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
