import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Governance benchmark: Voting
Source: Solidity documentation v0.8.26, voting example (Ballot):
<https://github.com/ethereum/solidity/blob/v0.8.26/docs/examples/voting.rst>.
This direct-vote benchmark retains the chairperson, voting weights, one-vote
flag and per-proposal tally. Delegation and proposal-name storage are excluded;
the proposal count is explicit instead of a string-array constructor argument.
It is a direct-vote variant, not a verification of the full delegated Ballot.
Natural @custom:key clauses cover authorization, one vote, and tally effects.
Verdicts: constructor, giveRightToVote, vote: proved.
-/
namespace Solidity.Examples.Benchmark.Governance.Voting
def Voting : Contract := contract!{
  address public chairperson;
  uint256 public proposalCount;
  mapping(address => uint256) public weight;
  mapping(address => bool) public voted;
  mapping(address => uint256) public choice;
  mapping(uint256 => uint256) public tally;
  ensures chairperson == msg.sender && proposalCount == count && weight[msg.sender] == 1;
  constructor(uint256 count) {
    chairperson = msg.sender;
    proposalCount = count;
    weight[msg.sender] = 1;
  }
  ensures msg.sender == chairperson && weight[voter] == 1 && !voted[voter];
  function giveRightToVote(address voter) public {
    require(msg.sender == chairperson);
    require(!voted[voter]);
    require(weight[voter] == 0);
    weight[voter] = 1;
  }
  ensures !\old(voted[msg.sender]) && voted[msg.sender] && choice[msg.sender] == proposal;
  ensures tally[proposal] == \old(tally[proposal]) + weight[msg.sender];
  ensures \forall uint256 p; p != proposal -> tally[p] == \old(tally[p]);
  function vote(uint256 proposal) public {
    require(weight[msg.sender] != 0);
    require(!voted[msg.sender]);
    require(proposal < proposalCount);
    voted[msg.sender] = true;
    choice[msg.sender] = proposal;
    tally[proposal] += weight[msg.sender];
  }
}
local instance : InContract := ⟨Voting⟩
open scoped Scoped
/-- `@custom:key` obligation for `constructor`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
/-- `@custom:key` obligation for `giveRightToVote`. -/
theorem spec_giveRightToVote : ⊢ spec!{ giveRightToVote } := by
  sol_prove
/-- `@custom:key` obligation for `vote`. -/
theorem spec_vote : ⊢ spec!{ vote } := by
  sol_prove
end Solidity.Examples.Benchmark.Governance.Voting
