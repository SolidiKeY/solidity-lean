import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Patterns benchmark: explicit state machine

Source: Solidity documentation v0.8.28, Common Patterns, "State Machine":
<https://github.com/ethereum/solidity/blob/v0.8.28/docs/common-patterns.rst>.

Changes: none but the spelling of `contract!{ … }` (each unbraced `if` body
braced); the error and comments are
dropped by elaboration. Stage members are their positions (0 to 4); a clause spells `10 days`
as `864000` and `12 days` as `1036800` seconds.
Natural `@custom:key` clauses: each function runs only at its stage (after the
timed transitions), and the stage only moves forward (`stage >= \old(stage)`).

Verdicts: g, h, i proved; bid, reveal unknown. `nextStage` is internal and
inlined, with no clause of its own.
-/
namespace Solidity.Examples.Benchmark.Patterns.StateMachine
def StateMachine : Contract := contract!{
  enum Stages { AcceptingBlindedBids, RevealBids, AnotherStage, AreWeDoneYet, Finished }
  error FunctionInvalidAtThisStage();
  Stages public stage = Stages.AcceptingBlindedBids;
  uint public creationTime = block.timestamp;
  modifier atStage(Stages stage_) {
    if (stage != stage_) {
      revert FunctionInvalidAtThisStage();
    }
    _;
  }
  function nextStage() internal {
    stage = Stages(uint(stage) + 1);
  }
  modifier timedTransitions() {
    if (stage == Stages.AcceptingBlindedBids && block.timestamp >= creationTime + 10 days) {
      nextStage();
    }
    if (stage == Stages.RevealBids && block.timestamp >= creationTime + 12 days) {
      nextStage();
    }
    _;
  }
  ensures stage == 0 && stage >= \old(stage) && block.timestamp < creationTime + 864000;
  function bid() public payable timedTransitions atStage(Stages.AcceptingBlindedBids) {
  }
  ensures stage == 1 && stage >= \old(stage) && block.timestamp < creationTime + 1036800;
  function reveal() public timedTransitions atStage(Stages.RevealBids) {
  }
  modifier transitionNext() {
    _;
    nextStage();
  }
  ensures stage == 3 && stage >= \old(stage) && \old(stage) <= 2;
  function g() public timedTransitions atStage(Stages.AnotherStage) transitionNext {
  }
  ensures stage == 4 && \old(stage) == 3;
  function h() public timedTransitions atStage(Stages.AreWeDoneYet) transitionNext {
  }
  ensures stage == 4 && \old(stage) == 4;
  function i() public timedTransitions atStage(Stages.Finished) {
  }
}
local instance : InContract := ⟨StateMachine⟩
open scoped Scoped
/-- Unknown: `sol_prove` and `sol_auto` leave the paths where the timed
transitions fired (stage saved as `stage + 1`, once or twice) and `atStage`
then read the saved stage: closing them needs the read-after-save stage
arithmetic (`find(save(s, stage, v), stage) = v`, `v = old + 1`) that refutes
`stage == 0` (and proves the enum range check `stage + 1 < 5`); the leaf
closer misses it. The full obligation is retained. -/
def bid_obligation : Fml StateMachine [] := spec!{ bid }
/-- Unknown: the same gap as `bid` (a saved stage read back after one or two
timed transitions). The full obligation is retained. -/
def reveal_obligation : Fml StateMachine [] := spec!{ reveal }
theorem spec_g : ⊢ spec!{ g } := by
  sol_prove
theorem spec_h : ⊢ spec!{ h } := by
  sol_prove
theorem spec_i : ⊢ spec!{ i } := by
  sol_prove
end Solidity.Examples.Benchmark.Patterns.StateMachine
