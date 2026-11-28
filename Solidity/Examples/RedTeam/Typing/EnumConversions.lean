import Solidity.Semantics.Run
import Solidity.Syntax.Splice

/-!
# An enum converts to and from `uint` implicitly

Claim: an enum is a `uint` to the elaborator, so it types three conversions
solc 0.8.38 rejects.

* `r = E.B;` with `r : uint` — solc: "Type enum T.E is not implicitly
  convertible to expected type uint256."
* `E e = 1;` — solc: "Type int_const 1 is not implicitly convertible to
  expected type enum T.E."
* `E e = E(5);` — solc: "Explicit type conversion not allowed from
  \"int_const 5\" to \"enum T.E\"."; the model runs it to a panic.

Culprit: `Solidity/Syntax/Elab/Context.lean:170` (`elabTy` reads an enum name
as `.uint`) and `Solidity/Syntax/Raw.lean:414` ("an enum is read as `uint`").
`Language.Feature.enumDeclarations` asks to "Preserve distinct enum identity".
Suggested fix: keep an enum marker row (as `enumRows` already does for
widths) and refuse an implicit conversion between it and any other type, and
an explicit conversion of an out-of-range literal.
-/

namespace Solidity.Examples.RedTeam.Typing.EnumConversions
open Solidity

def En : Contract := contract!{
  enum E { A, B }
  function toUint() public returns (uint r) { r = E.B; }
  function fromUint() public { E e = 1; }
  function big() public { E e = E(5); }
}

/-- `uint r = toUint(); fromUint(); assert(r == 1);` -/
def mix := sol[En]{ uint r = toUint(); fromUint(); assert(r == 1); }

/-- The implicit conversions run to the end. -/
theorem mix_runs : (Prog.run (State.ofStorage (Storage.init En)) mix).halt? = none := by
  decide +kernel

/-- `big();` — a compile-time error in solc, a panic here. -/
def bigRun := sol[En]{ big(); }

theorem big_panics :
    (Prog.run (State.ofStorage (Storage.init En)) bigRun).halt? = some .panic := by
  decide +kernel

end Solidity.Examples.RedTeam.Typing.EnumConversions
