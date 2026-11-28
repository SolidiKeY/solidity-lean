import Solidity.Calculus.Closers
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface

/-!
# solkey open problems: `SolcLoops`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/semantics/open/SolcLoops.sol>.
Changes: single-statement loop bodies braced.  `binomialFaithful`, `binomial` and their
obligations `binomialFaithfulRowsSmall`, `binomialRowsNine` are not restated: both are proved on the
imported source in `Examples/Tactics/OpenLoops.lean` and `Examples/Tactics/OpenLoops/RowsNine.lean`.
All five obligations here are tagged `@custom:key box`: `spec!{f}`.
-/

namespace Solidity.Examples.SolkeyOpen.SolcLoops

def SolcLoops : Contract := contract!{
  struct Nest { uint[][] d; }
  uint[][] array2d;
  Nest[] nests;
  function multiArrayFillByPushLoops() public {
    require(nests.length == 0);
    while (nests.length < 3) { nests.push(); }
    while (nests[2].d.length < 4) { nests[2].d.push(); }
    while (nests[2].d[3].length < 5) { nests[2].d[3].push(); }
    nests[2].d[3][4] = 8;
    uint r = nests[2].d[3][4];
    assert(r == 8);
    delete nests;
    uint l = nests.length;
    assert(l == 0);
  }
  function pushNoArgs2dLoop(uint index, uint value) public {
    require(index == 42 && value == 64);
    require(array2d.length == 0);
    uint[] storage pointer = array2d.push();
    for (uint i = 0; i <= index; ++i) { pointer.push(); }
    pointer[index] = value;
    uint l = array2d.length;
    uint ll = array2d[0].length;
    uint a = array2d[0][42];
    assert(l == 1);
    assert(ll == 43);
    assert(a == 64);
  }
  function doWhileContinueNeverLeaves() public pure {
    uint x;
    /// @custom:key invariant x == 0
    do { continue; x = 1; } while (x == 0);
    assert(x == 0);
  }
  function forTrivialConditionResetInBody(uint x) public pure {
    require(x == 2);
    uint y;
    /// @custom:key invariant x == 2
    for (; x == 2;) { x = 2; }
    assert(x == 2);
  }
  function forTrivialConditionUntouched(uint x) public pure {
    require(x == 2);
    uint y;
    /// @custom:key invariant x == 2
    for (; x == 2;) { y = 7; }
    assert(x == 2);
  }
}

local instance : InContract := ⟨SolcLoops⟩
open scoped Scoped

/-- Unknown: `sol_prove` unrolls the three push loops until its heartbeat limit (a timeout in its
compiled walk, after the 1024-step stage) and `sol_refute` finds no witness.  solkey: "exceeds the
suite budget".  Missing: an invariant for the loops, or a walk within the budget. -/
def multiArrayFillByPushLoops_obligation : Fml SolcLoops [] := spec!{ multiArrayFillByPushLoops }
/-- Unknown: `sol_prove` unrolls the 43 pushes until its heartbeat limit (after the 512-step stage),
`sol_prove (chunk := 128)` runs out of memory at 9 GB, and `sol_refute` finds no witness. -/
def pushNoArgs2dLoop_obligation : Fml SolcLoops [] := spec!{ pushNoArgs2dLoop }
/-- Proved (the invariant's leaves by `sol_close`): the box holds of a loop that never ends
(solkey: "closes in KeY, but the EVM run halts out of gas"). -/
theorem spec_doWhileContinueNeverLeaves : ⊢ spec!{ doWhileContinueNeverLeaves } := by
  sol_prove
  all_goals (sol_leaf; sol_close)
/-- Proved, as `doWhileContinueNeverLeaves`. -/
theorem spec_forTrivialConditionResetInBody : ⊢ spec!{ forTrivialConditionResetInBody } := by
  sol_prove
  all_goals (sol_leaf; sol_close)
/-- Proved, as `doWhileContinueNeverLeaves`. -/
theorem spec_forTrivialConditionUntouched : ⊢ spec!{ forTrivialConditionUntouched } := by
  sol_prove
  all_goals (sol_leaf; sol_close)

end Solidity.Examples.SolkeyOpen.SolcLoops
