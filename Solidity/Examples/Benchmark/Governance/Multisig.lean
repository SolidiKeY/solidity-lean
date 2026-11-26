import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Governance benchmark: Multisig
Source: Solidity by Example, MultiSigWallet, pinned revision:
<https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/app/multi-sig-wallet/MultiSigWallet.sol>.
This is the confirmation state machine for a fixed two-owner wallet, with
transaction IDs rather than a transaction struct array. Payloads are Ether
transfers (empty calldata); arbitrary calldata and callbacks are not modeled.
The threshold, distinct-owner membership, confirmation and revocation guards
are retained. No theorem claims execution of arbitrary external calldata.
Natural @custom:key clauses state no double confirmation and threshold checks.
Verdicts: constructor, revoke, execute proved; submit and confirm unknown.
-/
namespace Solidity.Examples.Benchmark.Governance.Multisig
def Multisig : Contract := contract!{
  address public firstOwner;
  address public secondOwner;
  uint256 public threshold;
  uint256 public transactionCount;
  mapping(uint256 => address) public recipient;
  mapping(uint256 => uint256) public amount;
  mapping(uint256 => uint256) public confirmations;
  mapping(uint256 => mapping(address => bool)) public confirmed;
  mapping(uint256 => bool) public executed;
  requires first != second && first != 0 && second != 0 && required > 0 && required <= 2;
  ensures firstOwner == first && secondOwner == second && threshold == required;
  constructor(address first, address second, uint256 required) {
    require(first != second && first != 0 && second != 0);
    require(required > 0 && required <= 2);
    firstOwner = first; secondOwner = second; threshold = required;
    transactionCount = 0;
  }
  ensures transactionCount == \old(transactionCount) + 1;
  ensures recipient[\old(transactionCount)] == to && amount[\old(transactionCount)] == value;
  ensures confirmations[\old(transactionCount)] == 0 && !executed[\old(transactionCount)];
  ensures !confirmed[\old(transactionCount)][firstOwner] && !confirmed[\old(transactionCount)][secondOwner];
  function submit(address to, uint256 value) public {
    require(msg.sender == firstOwner || msg.sender == secondOwner);
    recipient[transactionCount] = to; amount[transactionCount] = value;
    confirmations[transactionCount] = 0; executed[transactionCount] = false;
    confirmed[transactionCount][firstOwner] = false; confirmed[transactionCount][secondOwner] = false;
    transactionCount += 1;
  }
  ensures !\old(confirmed[id][msg.sender]) && confirmed[id][msg.sender];
  ensures confirmations[id] == \old(confirmations[id]) + 1 && !executed[id];
  ensures msg.sender == firstOwner || msg.sender == secondOwner;
  function confirm(uint256 id) public {
    require(msg.sender == firstOwner || msg.sender == secondOwner);
    require(id < transactionCount);
    require(!executed[id]);
    require(!confirmed[id][msg.sender]);
    confirmed[id][msg.sender] = true;
    confirmations[id] += 1;
  }
  ensures \old(confirmed[id][msg.sender]) && !confirmed[id][msg.sender];
  ensures confirmations[id] == \old(confirmations[id]) - 1 && !executed[id];
  function revoke(uint256 id) public {
    require(msg.sender == firstOwner || msg.sender == secondOwner);
    require(id < transactionCount);
    require(!executed[id]);
    require(confirmed[id][msg.sender]);
    confirmed[id][msg.sender] = false;
    confirmations[id] -= 1;
  }
  ensures !\old(executed[id]) && executed[id] && confirmations[id] >= threshold;
  function execute(uint256 id) public {
    require(msg.sender == firstOwner || msg.sender == secondOwner);
    require(id < transactionCount);
    require(!executed[id]);
    require(confirmations[id] >= threshold);
    executed[id] = true;
    (bool success, ) = recipient[id].call{value: amount[id]}("");
    require(success);
  }
}
local instance : InContract := ⟨Multisig⟩
open scoped Scoped
/-- `@custom:key` obligation for `constructor`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
/-- Unknown: the full fresh-ID initialization obligation is retained. The
`sol_prove` leaves both owner branches after multiple mapping writes at the
old transaction count; snapshot/index leaf normalization is missing. -/
def submit_obligation := spec!{ submit }
/-- Unknown: `sol_prove` leaves the second-owner branch with Boolean locals,
nested mapping aliases and the old-storage snapshot; the leaf closer is missing
normalization for this combination. The complete obligation is retained. -/
def confirm_obligation := spec!{ confirm }
/-- `@custom:key` obligation for `revoke`. -/
theorem spec_revoke : ⊢ spec!{ revoke } := by
  sol_prove
/-- `@custom:key` obligation for `execute`. -/
theorem spec_execute : ⊢ spec!{ execute } := by
  sol_prove
end Solidity.Examples.Benchmark.Governance.Multisig
