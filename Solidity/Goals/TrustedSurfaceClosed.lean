import Solidity.Tools.Goal

/-! The plan goal `trustedSurfaceClosed` (`va1-trust-surface`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Main.trusted_surface_closed "va1-trust-surface"]
def trustedSurfaceClosed : Prop := Unstated

end Solidity.Goals
