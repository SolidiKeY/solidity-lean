import Solidity.Goals

/--
info: proved Solidity.Goals.tacletsPartitioned ← Solidity.RuleShapes.taclets_partitioned
proved Solidity.Goals.compilerCorrectNoPaymentRevert ← Solidity.Main.compiler_correct_v2
mismatch Solidity.Goals.headlineIsNoPaymentRevert ← Solidity.Main.compiler_correct plan va2-honest-theorems
unstated Solidity.Goals.lowerLoopsCorrect ← Solidity.Correctness.Lowering.lowerLoops_correct plan e1-lowering
unstated Solidity.Goals.compilerCorrectCollisionFree ← Solidity.Hash.compiler_correct_collisionFree plan e4-hash-bridge
unstated Solidity.Goals.runCarriesPanicCodes ← Solidity.Semantics.run_panic_codes plan w3-panic-codes
-/
#guard_msgs in
#roadmap
