import Solidity.TestSuite.ScopedProblems



open Solidity
open scoped Scoped

theorem Solkey.TestSuite.testArrayCopyClearsOldElements.proved : ⊢ Solkey.TestSuite.testArrayCopyClearsOldElements.problem := by
  sol_prove
