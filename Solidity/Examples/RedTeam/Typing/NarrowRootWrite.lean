import Solidity.Semantics.Run
import Solidity.Syntax.Splice

/-!
# The typed syntax writes `300` to a `uint8` state variable

Claim: a narrow width is not part of a type: `uint8 s;` is a root of type
`uint` with the row `("s", 8)` in `Contract.widths`, which only the
elaborator reads. So the typed statement `s = 300;`, which solc 0.8.38
rejects ("Type int_const 300 is not implicitly convertible to expected type
uint8. Literal is too large to fit in uint8.") and the elaborator refuses,
is a `Stmt`, and its run leaves `s > 255`. The intrinsic syntax (Gate G0) does
not exclude it: anything consuming typed programs rather than elaborated ones
(rules, lowering, the calculus's `Fml.Valid` over every typed state, `#run …
with s := 300`) sees `uint8` roots outside their range.

Culprit: `Solidity/Syntax/Raw.lean:422` (`Contract.widths`, outside `Ty`) and
`Solidity/Syntax/Scoped.lean:43` (`Simple.lit` checks `PrimTy.inRange`, the
256-bit range, only). Suggested fix: either carry widths in `PrimTy` (an
intrinsic `uintN`), or state the width bound as a hypothesis/invariant
(`Contract.widths` respected by the state and by every `Src`), and check that
consumers of typed programs assume it.
-/

namespace Solidity.Examples.RedTeam.Typing.NarrowRootWrite
open Solidity

def Narrow : Contract := contract!{ uint8 s; }

/-- The width is recorded beside the type. -/
example : Narrow.widths = [("s", 8)] ∧ Narrow.rootType "s" = some .uint := by decide

/-- `s = 300; assert(s > 255);`, the write written as a typed statement. -/
def wide : Prog Narrow [] [] :=
  .cons (.assign (.root "s" rfl) (.val (.simple (.lit 300 (by decide)))))
    sol[Narrow]{ assert(s > 255); }

/-- The `uint8` root holds `300` after the run. -/
theorem wide_runs : (Prog.run (State.ofStorage (Storage.init Narrow)) wide).halt? = none := by
  decide +kernel

end Solidity.Examples.RedTeam.Typing.NarrowRootWrite
