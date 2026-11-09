import Solidity.Yul.Views.GenericFlow.Following

namespace Solidity.Yul.Views.GenericFlow.Following

variable {Inventory Raw Operation Plan : Type}
variable {shape : PreparationShape Inventory Raw Operation Plan}

/-- A failed actual decoder makes following preparation unsupported,
regardless of the new separation check. -/
theorem none_of_write_none (p : Following shape)
    (missing : shape.write? p.raw = none) : p.run? = none := by
  unfold run?
  split
  next checked =>
    split
    next absent => rfl
    next op prepared =>
      have impossible : none = some op := missing.symm.trans prepared
      cases impossible
  next rejected => rfl

end Solidity.Yul.Views.GenericFlow.Following
