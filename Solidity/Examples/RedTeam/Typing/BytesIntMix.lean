import Solidity.Semantics.Run
import Solidity.Syntax.Splice

/-!
# `bytesN` and `uintN` mix implicitly, and `bytesN` takes arithmetic

Claim: the elaborator types four forms solc 0.8.38 rejects, and runs them.

* `bytes1 b = a;` with `a : uint8` — solc: "Type uint8 is not implicitly
  convertible to expected type bytes1."
* `uint8 c = b;` with `b : bytes1` — solc: "Type bytes1 is not implicitly
  convertible to expected type uint8."
* `bytes2 d = 0x01;` — solc: "Type int_const 1 is not implicitly convertible
  to expected type bytes2." (a hex literal must have the type's byte length)
* `d + d` at `bytes1` — solc: "Built-in binary operator + cannot be applied to
  types bytes1 and bytes1."; the model runs it as checked `uint8` addition.

Culprit: `Solidity/Syntax/Elab/Context.lean:191` (`elabDeclTy` reads
`bytesN` as a `uint` of `8 * N` bits) with
`Solidity/Syntax/Elab/Values.lean:2779` (`fitCheck` compares widths only, not
the integer/`bytesN` kind its marker rows record) and
`Solidity/Syntax/Elab/Values.lean:419` (`BinOp.accepts` sees only `uint`).
`Language.Feature.fixedBytesTypes` and `.implicitConversions` are `limited`
without naming these. Suggested fix: refuse an implicit conversion and an
arithmetic operator wherever source and target `#bytes` rows differ, and a
hex literal whose digit count is not `2 * N` (other than `0`).
-/

namespace Solidity.Examples.RedTeam.Typing.BytesIntMix
open Solidity

def Mix : Contract := contract!{ }

/-- `uint8 a = 200; bytes1 b = a; uint8 c = b; bytes2 d = 0x01; assert(c == 200);` -/
def mix := sol[Mix]{
  uint8 a = 200; bytes1 b = a; uint8 c = b; bytes2 d = 0x01; assert(c == 200); }

/-- The conversions solc refuses run to the end. -/
theorem mix_runs : (Prog.run (State.ofStorage (Storage.init Mix)) mix).halt? = none := by
  decide +kernel

/-- `bytes1 d = 0x80; bytes1 e = d + d;` -/
def add := sol[Mix]{ bytes1 d = 0x80; bytes1 e = d + d; }

/-- The `bytes1` sum solc refuses to type runs, as an overflowing `uint8` sum. -/
theorem add_reverts :
    (Prog.run (State.ofStorage (Storage.init Mix)) add).halt? = some .revert := by
  decide +kernel

end Solidity.Examples.RedTeam.Typing.BytesIntMix
