import Solidity.Semantics.Run
import Solidity.Syntax.Splice

/-!
# `view`, `pure` and non-`payable` restrict nothing

Claim: the contract syntax reads a function's state mutability and drops it,
so the elaborator types three bodies solc 0.8.38 rejects, and the run
performs them.

* `function w() public view { x = 1; }` — solc: "Function cannot be declared
  as view because this expression (potentially) modifies the state."
* `function p() public pure returns (uint r) { r = x; }` — solc: "Function
  declared as pure, but this expression (potentially) reads from the
  environment or state and thus requires \"view\"."
* `function v() public returns (uint r) { r = msg.value; }` — solc:
  "\"msg.value\" and \"callvalue()\" can only be used in payable public
  functions."

Culprit: `Solidity/Syntax/Contract.lean:52` (`solAttrKw`: "a visibility or a
mutability (dropped)"). `Language.Feature.stateMutability` is `limited` and
asks to "Enforce static restrictions". Suggested fix: keep the mutability on
`FunDecl` and refuse, at elaboration, a storage write or a call of a
non-`view` function in a `view` body, any state or environment read in a
`pure` body, and `msg.value` outside a `payable` (or internal) function.
-/

namespace Solidity.Examples.RedTeam.Typing.Mutability
open Solidity

def Mut : Contract := contract!{
  uint x;
  function w() public view { x = 1; }
  function p() public pure returns (uint r) { r = x; }
  function v() public returns (uint r) { r = msg.value; }
}

/-- `w(); uint r = p(); uint s = v(); assert(x == 1); assert(r == 1);` -/
def run := sol[Mut]{ w(); uint r = p(); uint s = v(); assert(x == 1); assert(r == 1); }

/-- The `view` function wrote `x`, and the `pure` one read it. -/
theorem run_ok : (Prog.run (State.ofStorage (Storage.init Mut)) run).halt? = none := by
  decide +kernel

end Solidity.Examples.RedTeam.Typing.Mutability
