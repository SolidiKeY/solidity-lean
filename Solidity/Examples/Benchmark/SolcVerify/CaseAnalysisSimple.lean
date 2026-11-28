import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Run

/-!
# solc-verify: case-analysis postconditions

Source: <https://github.com/SRI-CSL/solidity/blob/8ea107cecd90ffff0d6a8f276b434b5ac9aa043b/test/solc-verify/specs/CaseAnalysisSimple.sol>.
Changes: `[case c: e; …]` is one `ensures \old(c) -> e` per case (a case
reads the entry state); the unbraced `if` bodies are braced.
-/

namespace Solidity.Examples.Benchmark.SolcVerify.CaseAnalysisSimple

/-- The source contract, with its clauses. -/
def CaseAnalysisSimple : Contract := contract!{
  int x;
  int y;
  ensures \old(x) > 0 -> y == 1;
  ensures \old(x) < 0 -> y == -1;
  function correct() public {
    if (x > 0) { y = 1; }
    else if (x < 0) { y = -1; }
  }
  ensures \old(x) > 0 -> y == 1;
  ensures \old(x) < 0 -> y == -1;
  function wrongdefault() public {
    if (x > 0) { y = 1; }
    y = -1;
  }
}
local instance : InContract := ⟨CaseAnalysisSimple⟩
open scoped Scoped

/-- `correct`: `y == 1` when `x > 0`, `y == -1` when `x < 0`. Proved. -/
theorem correct_spec : ⊢ spec!{ correct } := by sol_prove
/- `wrongdefault()` from `x == 1`: refuted, `y == -1`. -/
/--
info: ok
x = 1
y = -1
-/
#guard_msgs in #run CaseAnalysisSimple.wrongdefault() with x := 1

end Solidity.Examples.Benchmark.SolcVerify.CaseAnalysisSimple
