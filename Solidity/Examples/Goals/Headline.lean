import Solidity.Goals.Headline

namespace Solidity.Goals

/--
info: proved Solidity.Goals.compilerCorrectNoPaymentRevert ← Solidity.Main.compiler_correct_v2
mismatch Solidity.Goals.headlineIsNoPaymentRevert ← Solidity.Main.compiler_correct plan va2-honest-theorems
-/
#guard_msgs in
#roadmap_goal compilerCorrectNoPaymentRevert headlineIsNoPaymentRevert

end Solidity.Goals
