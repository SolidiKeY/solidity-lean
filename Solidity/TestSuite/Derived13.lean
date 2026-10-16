import Solidity.TestSuite.ScopedProblems

/-!
# Storage-copy derivation retained after the dangling-suite migration

Four former resurrection claims moved upstream to `StorageDanglingOpen.sol`.
Their source import and kernel refutations are in
`Solidity/Counterexamples/StorageDangling.lean`. They are no longer derived here.
The historical TestSuite fixture still lists them until its separate repin.
`testArrayCopyClearsOldElements` remains a valid storage-copy derivation.
-/

open Solidity
open scoped Scoped

theorem Solkey.TestSuite.testArrayCopyClearsOldElements.proved : ⊢ Solkey.TestSuite.testArrayCopyClearsOldElements.problem := by
  sol_prove
