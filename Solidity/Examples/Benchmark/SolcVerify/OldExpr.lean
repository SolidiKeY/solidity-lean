import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Counterexample

/-!
# solc-verify: `\old` in postconditions

Source: <https://github.com/SRI-CSL/solidity/blob/8ea107cecd90ffff0d6a8f276b434b5ac9aa043b/test/solc-verify/specs/OldExpr.sol>.
Changes: `__verifier_old_address(e)`, `__verifier_old_int(e)`,
`__verifier_old_uint(e)` are `\old(e)`; `@notice postcondition` is `ensures`;
arithmetic is checked (0.8), not solc-verify's default unbounded integers.
-/

namespace Solidity.Examples.Benchmark.SolcVerify.OldExpr

/-- The source contract, with its clauses. -/
def OldExpr : Contract := contract!{
  address owner;
  int256 counter;
  uint40 counter2;
  constructor() {
    owner = msg.sender;
  }
  ensures msg.sender == \old(owner) || owner == \old(owner);
  function changeOwnerCorrect(address newOwner) public {
    require(msg.sender == owner);
    owner = newOwner;
  }
  ensures msg.sender == \old(owner) || owner == \old(owner);
  function changeOwnerIncorrect(address newOwner) public {
    owner = newOwner;
  }
  ensures counter == \old(counter) + 1;
  ensures counter2 == \old(counter2) + 1;
  function increment() public {
    counter++;
    counter2++;
  }
}
local instance : InContract := ⟨OldExpr⟩
open scoped Scoped

/-- `changeOwnerCorrect`: only the owner changes the owner. Proved. -/
theorem changeOwnerCorrect_spec : ⊢ spec!{ changeOwnerCorrect } := by sol_prove
/-- `increment`: both counters step by one (an overflow reverts). Proved. -/
theorem increment_spec : ⊢ spec!{ increment } := by sol_prove
/-- The constructor has no clause. Proved. -/
theorem constructor_spec : ⊢ spec!{ constructor } := by sol_prove
/-- `changeOwnerIncorrect(7)` from `owner == 0`, sent by `5`: refuted,
`owner == 7` and neither disjunct holds. -/
theorem changeOwnerIncorrect_refuted : ¬ (⊢ spec!{ changeOwnerIncorrect }) := by sol_refute

end Solidity.Examples.Benchmark.SolcVerify.OldExpr
