import Solidity.TestSuite.ScopedProblems

/-!
# Storage-copy derivation retained after the dangling-suite migration

Four former resurrection claims moved upstream to `StorageDangling.sol`.
They are derived from that source in
`Solidity/Examples/Tactics/StorageDangling.lean`, not here.
The historical TestSuite fixture still lists them until its separate repin.
`testArrayCopyClearsOldElements` remains a valid storage-copy derivation.
-/

open Solidity
open scoped Scoped

theorem Solkey.TestSuite.testArrayCopyClearsOldElements.proved : ⊢ Solkey.TestSuite.testArrayCopyClearsOldElements.problem := by
  sol_prove
