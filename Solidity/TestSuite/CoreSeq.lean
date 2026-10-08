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
W3 lane `testsuite`).  Last, two diamond obligations whose leaf sits
behind a diamond update that sets a `bool` local from storage, which
`Proves.close` takes since the reading is the typed one (CORE B,
`docs/intrinsic.md`): an update's reading asks only of the typed states
that erase to the one it ends in, where a `bool` local holds a `bool`.
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

/-! ## Diamond obligations closed behind a diamond update

`flag = true; bool r = flag; assert(r);` under the diamond: the leaf is
behind `{r := select(…, flag)}`, a `bool` local set from storage, which the
closer could not take while the diamond read M3's states (decision 18's
interim `Upd.boolB`). -/

theorem Solkey.TestSuite.storageBoolRootReadWrite.proved_seq : ⊢ Solkey.TestSuite.storageBoolRootReadWrite.problem.core := by
  sol_prove

theorem Solkey.TestSuite.storageBoolFieldRead.proved_seq : ⊢ Solkey.TestSuite.storageBoolFieldRead.problem.core := by
  sol_prove
