import Solidity.Calculus.Core.SolSpec
import Solidity.Calculus.Core.Surface
import Solidity.Examples.Tactics.Specs

/-!
# `sol_spec` on scoped obligations

`Examples/Tactics/Specs.lean`'s obligations, scoped (`cspec!{f}`), proved by
the same `sol_spec` (`Calculus/Core/SolSpec.lean`): the scoped strategy,
then each leaf erased and closed as today's.  Under the switch
(`open scoped Solidity.Core.Surface`) the text is today's.
-/

namespace Solidity.Examples.Tactics.CoreSolSpec

open Solidity Examples.Tactics.Specs

local instance : InContract := ⟨ERC20⟩

theorem erc_approve : Core.Valid cspec!{ approve } := by sol_spec

section
open scoped Solidity.Core.Surface

theorem erc_approve' : ⊨ spec!{ approve } := by sol_spec

end

end Solidity.Examples.Tactics.CoreSolSpec
