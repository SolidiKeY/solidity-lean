import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (3 of 6)

`⊢` of each obligation `sol_prove` and its leaf tactics close, from
`storageIndexDeleteNseIndex` to `subtractionStorageRead` in the order of the source; the replays are what
`#solkey_derive?` (`Frontend/Problems.lean`) prints.  The closer reads
`wt(storage)` as the layout a well-formed storage holds; a leaf it leaves
sets the premise aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.storageIndexDeleteNseIndex.proved : ⊢ Solkey.TestSuite.storageIndexDeleteNseIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexDelete.proved : ⊢ Solkey.TestSuite.storageIndexDelete.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexDivAssign.proved : ⊢ Solkey.TestSuite.storageIndexDivAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexModAssign.proved : ⊢ Solkey.TestSuite.storageIndexModAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMulAssign.proved : ⊢ Solkey.TestSuite.storageIndexMulAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMultipleWrites.proved : ⊢ Solkey.TestSuite.storageIndexMultipleWrites.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPostdecrementAssign.proved : ⊢ Solkey.TestSuite.storageIndexPostdecrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPostdecrement.proved : ⊢ Solkey.TestSuite.storageIndexPostdecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPostincrementAssign.proved : ⊢ Solkey.TestSuite.storageIndexPostincrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPostincrement.proved : ⊢ Solkey.TestSuite.storageIndexPostincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPredecrementAssign.proved : ⊢ Solkey.TestSuite.storageIndexPredecrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPredecrement.proved : ⊢ Solkey.TestSuite.storageIndexPredecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPreincrementAssign.proved : ⊢ Solkey.TestSuite.storageIndexPreincrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPreincrement.proved : ⊢ Solkey.TestSuite.storageIndexPreincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexReadMappingStoreRoot.proved : ⊢ Solkey.TestSuite.storageIndexReadMappingStoreRoot.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexReadNseIndex.proved : ⊢ Solkey.TestSuite.storageIndexReadNseIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexSubAssign.proved : ⊢ Solkey.TestSuite.storageIndexSubAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexWriteNseChain.proved : ⊢ Solkey.TestSuite.storageIndexWriteNseChain.problem := by
  sol_prove

theorem Solkey.TestSuite.storageLocalDeclSkip.proved : ⊢ Solkey.TestSuite.storageLocalDeclSkip.problem := by
  sol_prove

theorem Solkey.TestSuite.storageMatrixNseIndex.proved : ⊢ Solkey.TestSuite.storageMatrixNseIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.storageMatrixWriteRead.proved : ⊢ Solkey.TestSuite.storageMatrixWriteRead.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootAddAssign.proved : ⊢ Solkey.TestSuite.storageRootAddAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootCopySource.proved : ⊢ Solkey.TestSuite.storageRootCopySource.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootDeleteStruct.proved : ⊢ Solkey.TestSuite.storageRootDeleteStruct.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootDelete.proved : ⊢ Solkey.TestSuite.storageRootDelete.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootDisjoint.proved : ⊢ Solkey.TestSuite.storageRootDisjoint.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootDivAssign.proved : ⊢ Solkey.TestSuite.storageRootDivAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootModAssign.proved : ⊢ Solkey.TestSuite.storageRootModAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootMulAssign.proved : ⊢ Solkey.TestSuite.storageRootMulAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootMultipleWrites.proved : ⊢ Solkey.TestSuite.storageRootMultipleWrites.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootPostdecrementAssign.proved : ⊢ Solkey.TestSuite.storageRootPostdecrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootPostincrementAssign.proved : ⊢ Solkey.TestSuite.storageRootPostincrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootPostincrement.proved : ⊢ Solkey.TestSuite.storageRootPostincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootPredecrement.proved : ⊢ Solkey.TestSuite.storageRootPredecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootPreincrementAssign.proved : ⊢ Solkey.TestSuite.storageRootPreincrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootPreincrement.proved : ⊢ Solkey.TestSuite.storageRootPreincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootSubAssign.proved : ⊢ Solkey.TestSuite.storageRootSubAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootWriteRhsCapture.proved : ⊢ Solkey.TestSuite.storageRootWriteRhsCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.subtractionSimple.proved : ⊢ Solkey.TestSuite.subtractionSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.subtractionStorageRead.proved : ⊢ Solkey.TestSuite.subtractionStorageRead.problem := by
  sol_prove
