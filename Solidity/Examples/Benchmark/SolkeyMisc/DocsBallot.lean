import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: solkey `DocsBallot`

Source: <https://github.com/SolidiKeY/solkey/blob/50a1469c8c34abf522c7027e47e6f53292d6920a/keyext.solidity.examples/contracts/real-world/DocsBallot.sol>,
itself from the Solidity documentation's `voting.rst` (commit `0944010b`).
The full delegated Ballot; `Examples/Benchmark/Governance/Voting.lean` is a
direct-vote variant without delegation.

Changes: none but the spelling of `contract!{ … }` and solkey's
`@custom:key` clauses; the contract invariants and `requires proposal >= 0`
(`>= 0` on a `uint`) hold for every typed state and are not restated.
-/

namespace Solidity.Examples.Benchmark.SolkeyMisc.DocsBallot

/-- solkey's `DocsBallot.sol`, with its clauses. -/
def DocsBallot : Contract := contract!{
  struct Voter {
    uint weight;
    bool voted;
    address delegate;
    uint vote;
  }
  struct Proposal {
    uint256 name;
    uint voteCount;
  }
  address public chairperson;
  mapping(address => Voter) public voters;
  Proposal[] public proposals;
  constructor(uint256[] memory proposalNames) {
    chairperson = msg.sender;
    voters[chairperson].weight = 1;
    uint256[] memory names = proposalNames;
    for (uint i = 0; i < names.length; i++) {
      proposals.push();
      proposals[proposals.length - 1].name = names[i];
      proposals[proposals.length - 1].voteCount = 0;
    }
  }
  ensures \old(chairperson) == msg.sender && chairperson == \old(chairperson);
  ensures \old(voters[voter].voted) == false && \old(voters[voter].weight) == 0;
  ensures voters[voter].weight == 1 && voters[voter].voted == false;
  function giveRightToVote(address voter) external {
    require(msg.sender == chairperson);
    require(!voters[voter].voted);
    require(voters[voter].weight == 0);
    voters[voter].weight = 1;
  }
  ensures \old(voters[msg.sender].weight) != 0 && \old(voters[msg.sender].voted) == false;
  ensures voters[msg.sender].voted == true && voters[msg.sender].delegate != msg.sender;
  ensures voters[voters[msg.sender].delegate].delegate == address(0);
  ensures \forall address d; d == voters[msg.sender].delegate && \old(voters[d].voted) == false -> voters[d].weight == \old(voters[d].weight) + \old(voters[msg.sender].weight);
  ensures \forall address d; \forall uint v; d == voters[msg.sender].delegate && \old(voters[d].voted) == true && v == voters[d].vote -> proposals[v].voteCount == \old(proposals[v].voteCount) + \old(voters[msg.sender].weight);
  function delegate(address to) external {
    Voter storage sender = voters[msg.sender];
    require(sender.weight != 0);
    require(!sender.voted);
    require(to != msg.sender);
    /// @custom:key invariant to != msg.sender
    while (voters[to].delegate != address(0)) {
      to = voters[to].delegate;
      require(to != msg.sender);
    }
    Voter storage delegate_ = voters[to];
    require(delegate_.weight >= 1);
    sender.voted = true;
    sender.delegate = to;
    if (delegate_.voted) {
      uint w = sender.weight;
      proposals[delegate_.vote].voteCount += w;
    } else {
      uint w = sender.weight;
      delegate_.weight += w;
    }
  }
  ensures \old(voters[msg.sender].weight) != 0 && \old(voters[msg.sender].voted) == false;
  ensures voters[msg.sender].voted == true && voters[msg.sender].vote == proposal;
  ensures proposals[proposal].voteCount == \old(proposals[proposal].voteCount) + \old(voters[msg.sender].weight);
  function vote(uint proposal) external {
    Voter storage sender = voters[msg.sender];
    require(sender.weight != 0);
    require(!sender.voted);
    sender.voted = true;
    sender.vote = proposal;
    uint w = sender.weight;
    proposals[proposal].voteCount += w;
  }
  ensures winningProposal_ == 0 || winningProposal_ < proposals.length;
  ensures \forall uint i; 0 <= i && i < proposals.length -> proposals[i].voteCount <= proposals[winningProposal_].voteCount;
  function winningProposal() public view returns (uint winningProposal_) {
    uint winningVoteCount = 0;
    /// @custom:key invariant 0 <= p && p <= proposals.length && (winningProposal_ == 0 || winningProposal_ < p)
    /// @custom:key invariant \forall uint i; 0 <= i && i < p -> proposals[i].voteCount <= winningVoteCount
    /// @custom:key invariant winningVoteCount == 0 && winningProposal_ == 0 || winningVoteCount == proposals[winningProposal_].voteCount
    for (uint p = 0; p < proposals.length; p++) {
      if (proposals[p].voteCount > winningVoteCount) {
        winningVoteCount = proposals[p].voteCount;
        winningProposal_ = p;
      }
    }
  }
  ensures \exists uint i; 0 <= i && i < proposals.length && winnerName_ == proposals[i].name;
  ensures \forall uint i; 0 <= i && i < proposals.length -> (\exists uint w; 0 <= w && w < proposals.length && winnerName_ == proposals[w].name && proposals[i].voteCount <= proposals[w].voteCount);
  ensures \exists uint w; 0 <= w && w < proposals.length && winnerName_ == proposals[w].name && (\forall uint i; 0 <= i && i < proposals.length -> proposals[i].voteCount <= proposals[w].voteCount);
  function winnerName() external view returns (uint256 winnerName_) {
    winnerName_ = proposals[winningProposal()].name;
  }
}

local instance : InContract := ⟨DocsBallot⟩

open scoped Scoped

/-- `giveRightToVote(voter)`: all three clauses. -/
theorem spec_giveRightToVote : ⊢ spec!{ giveRightToVote } := by
  sol_prove

/-- `vote(proposal)`: all three clauses. -/
theorem spec_vote : ⊢ spec!{ vote } := by
  sol_prove

/-- `delegate(to)`'s five clauses, as solkey states them. -/
def delegate_obligation : Fml DocsBallot [] := spec!{ delegate }
/- Unknown: `sol_prove` leaves three leaves.  Loop preservation of
`to != msg.sender` (true from `require(to != msg.sender)` in the body) prints
with a `‹Tm.app2 (Op2.binop BinOp.neB …) …›` escape over the anonymised loop
variable; the two exit leaves need `find` through the saves at the storage
references `sp2 = voters[msg.sender]`, `sp3 = voters[to]` (`to != msg.sender`)
and `proposals[vote].voteCount`, read back under the quantified `d`, `v`.
`sol_leaf; sol_close` hits `simp`'s recursion limit.  Missing: the printer
case for a comparison on an anonymised local, and a closer for reads through
struct-member saves at distinct mapping keys under a quantifier. -/

/-- `winningProposal()`'s two clauses, as solkey states them. -/
def winningProposal_obligation : Fml DocsBallot [] := spec!{ winningProposal }
/- Unknown: the loop leaves (preservation of the three solkey invariants, and
their use at exit) print with `‹…›` escapes (`0 <= p`, `p <= proposals.length`,
`winningProposal_ < p` over the anonymised loop variables); `sol_leaf;
sol_close` exhausts the heartbeat budget.  Missing: the printer case and a
closer for quantified array-prefix invariants across a conditional update. -/

/-- `winnerName()`'s three clauses, as solkey states them. -/
def winnerName_obligation : Fml DocsBallot [] := spec!{ winnerName }
/- Unknown: the inlined `winningProposal()` loop leaves the same invariant
leaves as above, and the exit leaf needs the witness `i := winningProposal_`
with `winningProposal_ < proposals.length` (the read `proposals[0]` on an
empty array reverts, so the box holds there).  Missing: `∃`-instantiation in
the closer (the other two clauses take the same witness). -/

end Solidity.Examples.Benchmark.SolkeyMisc.DocsBallot
