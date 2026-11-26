import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Governance benchmark: Timelock
Source: OpenZeppelin Contracts v4.9.6, governance/TimelockController.sol:
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v4.9.6/contracts/governance/TimelockController.sol>.
This operation timelock uses explicit operation IDs, owner instead
of role membership, and Ether transfers instead of arbitrary calldata.
Its queue/cancel/execute lifecycle keeps the source's ready-time check and
one-shot execution. It does not model hashing, batches, roles or predecessors.
Natural @custom:key clauses state the successful lifecycle effects; no early
execution and no replay are required by execute's postcondition.
Verdicts: constructor, schedule, cancel, execute: proved.
-/
namespace Solidity.Examples.Benchmark.Governance.Timelock
def Timelock : Contract := contract!{
  address public owner;
  uint256 public minDelay;
  mapping(uint256 => address) public recipient;
  mapping(uint256 => uint256) public amount;
  mapping(uint256 => uint256) public readyAt;
  mapping(uint256 => bool) public queued;
  mapping(uint256 => bool) public done;
  ensures owner == msg.sender && minDelay == delay;
  constructor(uint256 delay) { owner = msg.sender; minDelay = delay; }
  ensures msg.sender == owner && queued[id] && readyAt[id] == block.timestamp + delay;
  ensures delay >= minDelay && !\old(queued[id]) && !done[id];
  ensures recipient[id] == to && amount[id] == value;
  function schedule(uint256 id, uint256 delay, address to, uint256 value) public {
    require(msg.sender == owner);
    require(!queued[id] && !done[id]);
    require(delay >= minDelay);
    recipient[id] = to; amount[id] = value;
    readyAt[id] = block.timestamp + delay;
    queued[id] = true;
  }
  ensures msg.sender == owner && !queued[id] && \old(queued[id]);
  function cancel(uint256 id) public {
    require(msg.sender == owner);
    require(queued[id]);
    queued[id] = false;
  }
  ensures \old(queued[id]) && !queued[id] && done[id] && !\old(done[id]) && block.timestamp >= readyAt[id];
  ensures block.timestamp >= \old(readyAt[id]);
  function execute(uint256 id) public {
    require(queued[id] && !done[id]);
    require(block.timestamp >= readyAt[id]);
    (bool success, ) = recipient[id].call{value: amount[id]}("");
    require(success);
    require(queued[id] && !done[id]);
    require(block.timestamp >= readyAt[id]);
    queued[id] = false;
    done[id] = true;
  }
}
local instance : InContract := ⟨Timelock⟩
open scoped Scoped
/-- `@custom:key` obligation for `constructor`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
/-- `@custom:key` obligation for `schedule`. -/
theorem spec_schedule : ⊢ spec!{ schedule } := by
  sol_prove
/-- `@custom:key` obligation for `cancel`. -/
theorem spec_cancel : ⊢ spec!{ cancel } := by
  sol_prove
/-- `@custom:key` obligation for `execute`. -/
theorem spec_execute : ⊢ spec!{ execute } := by
  sol_prove
end Solidity.Examples.Benchmark.Governance.Timelock
