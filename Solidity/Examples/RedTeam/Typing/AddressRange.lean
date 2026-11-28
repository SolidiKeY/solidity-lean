import Solidity.Semantics.Run
import Solidity.Syntax.Splice

/-!
# An `address` holds a 200-bit value, and takes arithmetic

Claim: the elaborator types two declarations solc 0.8.38 rejects, and the
typed run then holds an `address` value at or above `2^160`.

* `address a = 2^200;` — solc: "Type int_const 1606…1376 is not implicitly
  convertible to expected type address."
* `address b = a + 1;` — solc: "Arithmetic operations on addresses are not
  supported."

The run below ends normally with `b > 2^160 - 1`, a value no address has
(`Language.Feature.addressTypes` asks for "bounded 160-bit identities").

Culprit: `Solidity/AST.lean:48` (`PrimTy.ofName?` reads `address` as `uint`)
and `Solidity/Syntax/Elab/Context.lean:194` (`elabDeclTy` gives `address` the
width 256, so neither the literal check nor the narrow capture bounds it).
Suggested fix: carry `address` as a width-160 `uint` with a marker row that
refuses arithmetic, ordering against numbers and implicit conversion from an
integer, as `bytesTy?` rows mark `bytesN`.
-/

namespace Solidity.Examples.RedTeam.Typing.AddressRange
open Solidity

def Addr : Contract := contract!{ }

/-- `address a = 2^200; address b = a + 1; assert(b > 2^160 - 1);` -/
def wide := sol[Addr]{
  address a = 1606938044258990275541962092341162602522202993782792835301376;
  address b = a + 1;
  assert(b > 1461501637330902918203684832716283019655932542975); }

/-- The run ends normally: the `address` `b` is above every 160-bit value. -/
theorem wide_runs : (Prog.run (State.ofStorage (Storage.init Addr)) wide).halt? = none := by
  decide +kernel

end Solidity.Examples.RedTeam.Typing.AddressRange
