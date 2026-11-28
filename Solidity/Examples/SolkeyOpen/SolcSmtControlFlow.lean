import Solidity.Calculus.Closers
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface

/-!
# solkey open problems: `SolcSmtControlFlow`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/semantics/open/SolcSmtControlFlow.sol>.
Changes: none (comments dropped).  A function solkey tags `@custom:key box` or specifies has the obligation `spec!{f}`; an untagged
one solkey's diamond, `msg.value == 0 → wt(storage) → ⟨ f(); ⟩ true`.
Both close: the premise of a function that is not `payable` is `msg.value == 0`, and
`msg.value` is a `uint`.
-/

namespace Solidity.Examples.SolkeyOpen.SolcSmtControlFlow

def SolcSmtControlFlow : Contract := contract!{
  uint counter;
  bool flag;
  function gAddr() internal pure returns (address) { address a; a = address(0); return a; }
  function readValue() internal view returns (uint) { return msg.value; }
  function msgValueZeroWhenNonPayable() public view { uint v = readValue(); assert(v == 0); }
  function msgValueNonNegative() public payable { uint v = msg.value; assert(v >= 0); }
}

local instance : InContract := ⟨SolcSmtControlFlow⟩
open scoped Scoped

/-- solkey: "a non-payable function does not fix msg.value to 0".  Proved. -/
theorem total_msgValueZeroWhenNonPayable : ⊢ dl!{ msg.value == 0 → wt(storage) → ⟨ msgValueZeroWhenNonPayable(); ⟩ true } := by sol_prove
/-- solkey: "msg.value is not known to be non-negative".  Proved (payable). -/
theorem total_msgValueNonNegative : ⊢ dl!{ msg.value < 340282366920938463463374607431768211456 → wt(storage) → ⟨ msgValueNonNegative(); ⟩ true } := by sol_prove

end Solidity.Examples.SolkeyOpen.SolcSmtControlFlow
