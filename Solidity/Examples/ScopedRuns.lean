import Solidity.Semantics.Run
import Solidity.Syntax.Splice

/-!
# Scoped programs, run

Scoped programs run on typed states: the storage the contract deploys with,
no memory, no locals.  They are written in `sol[C]{ … }`, which the
elaborator reads, so they sit here, above the core, and not beside the run
in `Semantics/Run.lean` (`docs/parallelism.md`).
-/

namespace Solidity

open Semantics (Selector lookupBy setBy ExtKey ExtResult structDef)

variable {C : Contract}

section Examples

def guardLowCore := sol[StandardExample]{ require(age > 3); }
def assertLowCore := sol[StandardExample]{ assert(age > 3); }
def incOrderCore := sol[TestSuite]{ uint i = 1; uint x = i++ + i; assert(x == 2); assert(i == 2); }
def indexOrderCore := sol[TestSuite]{ uint i = 0; values.push(100);
  values.push(100); values.push(100); values[++i] = ++i; assert(values[2] == 1); }

/-- A failing guard reverts. -/
example : (Prog.run (State.ofStorage Storage.standardExample) guardLowCore).halt? =
    some .revert := by
  decide +kernel

/-- A failing assertion panics. -/
example : (Prog.run (State.ofStorage Storage.standardExample) assertLowCore).halt? =
    some .panic := by
  decide +kernel

/-- solc's order of `++` inside an expression. -/
example : (Prog.run (State.ofStorage Storage.testSuite) incOrderCore).halt? = none := by
  decide +kernel

example : (Prog.run (State.ofStorage Storage.testSuite) indexOrderCore).halt? = none := by
  decide +kernel

/-- The calls of `CallsExample`: `addTwo(3)` is `5`, `larger(5, 7)` is `7`. -/
example : (match Prog.run (State.ofStorage (Storage.init CallsExample)) callsCore with
    | .ok o => some ((TEnv.get .here o.st.env : PrimTy.uint.Denote).1,
        (TEnv.get (.there .here) o.st.env : PrimTy.uint.Denote).1)
    | .error _ => none) = some (7, 5) := by
  decide +kernel

end Examples


end Solidity
