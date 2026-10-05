import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (4 of 11)

`⊢` of each obligation `sol_prove` and its leaf tactics close, from
`unaryMinusSimple` to `mappingReadAsKey` in the order of the source; the replays are what
`#solkey_derive?` (`Frontend/Problems.lean`) prints.  The closer reads
`wt(storage)` as the layout a well-formed storage holds; a leaf it leaves
sets the premise aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.unaryMinusSimple.proved : ⊢ Solkey.TestSuite.unaryMinusSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.testNestedStorageWrites.proved : ⊢ Solkey.TestSuite.testNestedStorageWrites.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageAliases.proved : ⊢ Solkey.TestSuite.testStorageAliases.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageArrayReadWrite.proved : ⊢ Solkey.TestSuite.testStorageArrayReadWrite.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageDeletePaperCase.proved : ⊢ Solkey.TestSuite.testStorageDeletePaperCase.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageMapReadWriteAndDelete.proved : ⊢ Solkey.TestSuite.testStorageMapReadWriteAndDelete.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageIndexDeleteOutOfBoundsReverts.proved : ⊢ Solkey.TestSuite.testStorageIndexDeleteOutOfBoundsReverts.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedArrayDeleteKeepsLength.proved : ⊢ Solkey.TestSuite.testFixedArrayDeleteKeepsLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedArrayLength.proved : ⊢ Solkey.TestSuite.testFixedArrayLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedArrayIndexInBounds.proved : ⊢ Solkey.TestSuite.testFixedArrayIndexInBounds.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedStructArrayLength.proved : ⊢ Solkey.TestSuite.testFixedStructArrayLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testStructFixedMemberLength.proved : ⊢ Solkey.TestSuite.testStructFixedMemberLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedElementOfDynamicArrayLength.proved : ⊢ Solkey.TestSuite.testFixedElementOfDynamicArrayLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testMappingOfFixedArrayLength.proved : ⊢ Solkey.TestSuite.testMappingOfFixedArrayLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedStructArrayDeleteResetsElements.proved : ⊢ Solkey.TestSuite.testFixedStructArrayDeleteResetsElements.problem := by
  sol_prove

theorem Solkey.TestSuite.testStructWithFixedArrayDeleteKeepsLength.proved : ⊢ Solkey.TestSuite.testStructWithFixedArrayDeleteKeepsLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedMappingArrayDeleteKeepsEntries.proved : ⊢ Solkey.TestSuite.testFixedMappingArrayDeleteKeepsEntries.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageStructDeleteSkipsMappingMember.proved : ⊢ Solkey.TestSuite.testStorageStructDeleteSkipsMappingMember.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageWriteAndRead.proved : ⊢ Solkey.TestSuite.testStorageWriteAndRead.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDecomposition.proved : ⊢ Solkey.TestSuite.storageFieldDecomposition.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDeepValue.proved : ⊢ Solkey.TestSuite.storageFieldDeepValue.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexDecomposition.proved : ⊢ Solkey.TestSuite.storageIndexDecomposition.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexRootArray.proved : ⊢ Solkey.TestSuite.storageIndexRootArray.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDisjointFields.proved : ⊢ Solkey.TestSuite.storageFieldDisjointFields.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDisjointRoots.proved : ⊢ Solkey.TestSuite.storageFieldDisjointRoots.problem := by
  sol_prove

theorem Solkey.TestSuite.storageAliasRebindOriginal.proved : ⊢ Solkey.TestSuite.storageAliasRebindOriginal.problem := by
  sol_prove

theorem Solkey.TestSuite.testSimpleAssert.proved : ⊢ Solkey.TestSuite.testSimpleAssert.problem := by
  sol_prove

theorem Solkey.TestSuite.localArithmeticInRange.proved : ⊢ Solkey.TestSuite.localArithmeticInRange.problem := by
  sol_prove

theorem Solkey.TestSuite.signedUnaryMinusInRange.proved : ⊢ Solkey.TestSuite.signedUnaryMinusInRange.problem := by
  sol_prove

theorem Solkey.TestSuite.additionLeftImpureRightReadFirst.proved : ⊢ Solkey.TestSuite.additionLeftImpureRightReadFirst.problem := by
  sol_prove

theorem Solkey.TestSuite.additionRightImpure.proved : ⊢ Solkey.TestSuite.additionRightImpure.problem := by
  sol_prove

theorem Solkey.TestSuite.additionBothOperandsImpure.proved : ⊢ Solkey.TestSuite.additionBothOperandsImpure.problem := by
  sol_prove

theorem Solkey.TestSuite.subtractionLeftImpureRightReadFirst.proved : ⊢ Solkey.TestSuite.subtractionLeftImpureRightReadFirst.problem := by
  sol_prove

theorem Solkey.TestSuite.lessThanLeftImpureRightReadFirst.proved : ⊢ Solkey.TestSuite.lessThanLeftImpureRightReadFirst.problem := by
  sol_prove

theorem Solkey.TestSuite.testCopyPrimitiveRoot.proved : ⊢ Solkey.TestSuite.testCopyPrimitiveRoot.problem := by
  sol_prove

theorem Solkey.TestSuite.nestedMappingWriteRead.proved : ⊢ Solkey.TestSuite.nestedMappingWriteRead.problem := by
  sol_prove

theorem Solkey.TestSuite.nestedMappingRowAlias.proved : ⊢ Solkey.TestSuite.nestedMappingRowAlias.problem := by
  sol_prove

theorem Solkey.TestSuite.mappingOfLedgerMember.proved : ⊢ Solkey.TestSuite.mappingOfLedgerMember.problem := by
  sol_prove

theorem Solkey.TestSuite.mappingPointerTernary.proved : ⊢ Solkey.TestSuite.mappingPointerTernary.problem := by
  sol_prove

theorem Solkey.TestSuite.mappingReadAsKey.proved : ⊢ Solkey.TestSuite.mappingReadAsKey.problem := by
  sol_prove
