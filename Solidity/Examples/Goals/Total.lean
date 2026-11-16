import Solidity.Backend.CompilerTotal

/-! Pins compiler totality as proved by `Solidity.Backend.compiler_total` itself: the
guard fails if the goal is still open, or if it is counted through a weakened, mismatched
or assumed (`sorry`, axiom) theorem. -/

namespace Solidity.Goals

/--
info: proved Solidity.Goals.compilerTotal ← Solidity.Backend.compiler_total plan t0-endpoint-total
-/
#guard_msgs in
#roadmap_goal compilerTotal

end Solidity.Goals
