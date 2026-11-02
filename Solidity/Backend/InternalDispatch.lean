import Solidity.Backend.InternalDispatch.FrozenV2
import Solidity.Backend.InternalDispatch.FrozenV3

/-! G37.03/P4 typed dispatch. FrozenV3 consumes exact P1 v3 ordinary-call admission and execution.
FrozenV2 remains available for older conditional interfaces. ObservationModel
is a separate independent Source model, not physical runtime-frame lowering. -/
