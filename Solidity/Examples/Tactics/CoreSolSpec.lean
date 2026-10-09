import Solidity.Calculus.SolSpec
import Solidity.Calculus.Surface
import Solidity.Examples.Tactics.Specs

/-!
# `sol_spec` on scoped obligations

`Examples/Tactics/Specs.lean`'s obligations, scoped (`cspec!{f}`), proved by
the same `sol_spec` (`Calculus/SolSpec.lean`): the scoped strategy,
then each leaf erased and closed as today's.  Under the switch
(`open scoped Solidity.Scoped`) the text is today's.
-/

namespace Solidity.Examples.Tactics.CoreSolSpec

open Solidity Examples.Tactics.Specs

section
local instance : InContract := ⟨ERC20⟩
theorem erc_approve : Valid cspec!{ approve } := by sol_spec
set_option maxHeartbeats 700000 in
theorem erc_mint : Valid cspec!{ _mint } := by sol_spec
end

section
local instance : InContract := ⟨Tally⟩
theorem tally_inc : Valid cspec!{ inc } := by sol_spec
theorem tally_mark : Valid cspec!{ mark } := by sol_spec
theorem tally_pay : Valid cspec!{ pay } := by sol_spec
end

section
local instance : InContract := ⟨Ordered⟩
open scoped Scoped
theorem ordered_inc : ⊨ spec!{ inc } := by sol_spec
theorem ordered_order : ⊨ spec!{ order } := by sol_spec
end

end Solidity.Examples.Tactics.CoreSolSpec
