import Solidity.TestSuite.ScopedProblems

/-! Native modular arithmetic and reference-parameter migration proofs. -/

open Solidity
open scoped Scoped

theorem Solkey.TestSuite.addmodMulmod.proved : ⊢ Solkey.TestSuite.addmodMulmod.problem := by
  sol_prove (steps := 128)

theorem Solkey.TestSuite.indexParameter.proved : ⊢ Solkey.TestSuite.indexParameter.problem := by
  sol_prove (steps := 256)

theorem Solkey.TestSuite.storageStructParameter.proved :
    ⊢ Solkey.TestSuite.storageStructParameter.problem := by
  sol_prove (steps := 256)

theorem Solkey.TestSuite.storageMappingParameter.proved :
    ⊢ Solkey.TestSuite.storageMappingParameter.problem := by
  sol_prove (steps := 256)

theorem Solkey.TestSuite.fileLevelStructThroughLibrary.proved :
    ⊢ Solkey.TestSuite.fileLevelStructThroughLibrary.problem := by
  sol_prove (steps := 256)

theorem Solkey.TestSuite.storageStaticToDynamicCopyKeepsLength.proved :
    ⊢ Solkey.TestSuite.storageStaticToDynamicCopyKeepsLength.problem := by
  sol_prove (steps := 256)

theorem Solkey.TestSuite.storageShorterStaticCopyClearsTail.proved :
    ⊢ Solkey.TestSuite.storageShorterStaticCopyClearsTail.problem := by
  sol_prove (steps := 256)

theorem Solkey.TestSuite.testFixedCopyThenEmptyPushReadsZero.proved :
    ⊢ Solkey.TestSuite.testFixedCopyThenEmptyPushReadsZero.problem := by
  sol_prove (steps := 256)

theorem Solkey.TestSuite.testShorterCopyThenEmptyPushClearsTail.proved :
    ⊢ Solkey.TestSuite.testShorterCopyThenEmptyPushClearsTail.problem := by
  sol_prove (steps := 256)

theorem Solkey.TestSuite.testShapeCopyFixedTailAndSourceIndependence.proved :
    ⊢ Solkey.TestSuite.testShapeCopyFixedTailAndSourceIndependence.problem := by
  sol_prove (steps := 256)
