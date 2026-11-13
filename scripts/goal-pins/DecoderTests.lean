import Solidity.Tools.GoalPins
open Solidity.Goals.GoalPinSpecV2 Solidity.GoalPins.Draft

-- A canonical decision and a 32-byte digest decode; malformed rows fail closed.
#guard match decodeRow ⟨`example, List.replicate 32 0, "H42"⟩ with
  | .ok pin => pin.decision == 42
  | .error _ => false
#guard match decodeRow ⟨`example, List.replicate 32 0, "H042"⟩ with
  | .error .malformedPin => true
  | _ => false
#guard match decodeRow ⟨`example, 256 :: List.replicate 31 0, "H42"⟩ with
  | .error .malformedPin => true
  | _ => false
