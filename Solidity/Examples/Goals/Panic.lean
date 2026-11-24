import Solidity.Correctness.Panic.Main

namespace Solidity.Goals

/--
info: proved Solidity.Goals.runCarriesPanicCodes ← Solidity.Semantics.run_panic_codes plan w3b-panic-bind
-/
#guard_msgs in
#roadmap_goal runCarriesPanicCodes

example : Solidity.Goals.runCarriesPanicCodes := Solidity.Semantics.run_panic_codes

end Solidity.Goals
