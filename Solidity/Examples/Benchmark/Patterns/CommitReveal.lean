import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Patterns benchmark: commit-reveal

Source: Solidity by Example, "Front Running", `SecuredFindThisHash`, pinned revision:
<https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/hacks/front-running/PreventFrontRunning.sol>.

Changes: none but the spelling of `contract!{ … }`; messages are dropped and
`revert("…")` is `revert();` by elaboration. Natural `@custom:key`
clauses: one commit per account, stamped with the time; a reveal in a later
block, matching the commitment, ends the game for the revealer.

Verdicts: constructor, commitSolution proved; getMySolution proved for its
guard only (its tuple cannot be named by a clause); revealSolution unknown.
-/
namespace Solidity.Examples.Benchmark.Patterns.CommitReveal
def SecuredFindThisHash : Contract := contract!{
  struct Commit {
    bytes32 solutionHash;
    uint256 commitTime;
    bool revealed;
  }
  bytes32 public hash = 0x564ccaf7594d66b1eaaea24fe01f0585bf52ee70852af4eac0cc4b04711cd0e2;
  address public winner;
  uint256 public reward;
  bool public ended;
  mapping(address => Commit) commits;
  modifier gameActive() {
    require(!ended, "Already ended");
    _;
  }
  ensures reward == msg.value;
  constructor() payable {
    reward = msg.value;
  }
  ensures !ended && \old(commits[msg.sender].commitTime) == 0;
  ensures commits[msg.sender].solutionHash == _solutionHash && commits[msg.sender].commitTime == block.timestamp;
  ensures !commits[msg.sender].revealed;
  function commitSolution(bytes32 _solutionHash) public gameActive {
    Commit storage commit = commits[msg.sender];
    require(commit.commitTime == 0, "Already committed");
    commit.solutionHash = _solutionHash;
    commit.commitTime = block.timestamp;
    commit.revealed = false;
  }
  ensures !ended && commits[msg.sender].commitTime != 0;
  function getMySolution() public view gameActive returns (bytes32, uint256, bool) {
    Commit storage commit = commits[msg.sender];
    require(commit.commitTime != 0, "Not committed yet");
    return (commit.solutionHash, commit.commitTime, commit.revealed);
  }
  ensures !\old(ended) && ended && winner == msg.sender;
  ensures \old(commits[msg.sender].commitTime) != 0 && \old(commits[msg.sender].commitTime) < block.timestamp;
  ensures !\old(commits[msg.sender].revealed);
  function revealSolution(string memory _solution, string memory _secret) public gameActive {
    Commit storage commit = commits[msg.sender];
    require(commit.commitTime != 0, "Not committed yet");
    require(commit.commitTime < block.timestamp, "Cannot reveal in the same block");
    require(!commit.revealed, "Already committed and revealed");
    bytes32 solutionHash = keccak256(abi.encodePacked(msg.sender, _solution, _secret));
    require(solutionHash == commit.solutionHash, "Hash doesn't match");
    require(keccak256(abi.encodePacked(_solution)) == hash, "Incorrect answer");
    winner = msg.sender;
    ended = true;
    (bool sent,) = payable(msg.sender).call{value: reward}("");
    if (!sent) {
      winner = address(0);
      ended = false;
      revert("Failed to send ether.");
    }
  }
}
local instance : InContract := ⟨SecuredFindThisHash⟩
open scoped Scoped
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
theorem spec_commitSolution : ⊢ spec!{ commitSolution } := by
  sol_prove
/-- The guard only: a clause cannot name the three unnamed returns
(`\result` needs one return, and `result__ret0` is not a clause name). -/
theorem spec_getMySolution : ⊢ spec!{ getMySolution } := by
  sol_prove
/-- Unknown: `sol_prove` exhausts the default heartbeats in its compiled walk
(after the 16384-step stage) on the two `keccak256(abi.encodePacked(…))`
string hashes, the struct reads and the payment with its failure branch. -/
def revealSolution_obligation : Fml SecuredFindThisHash [] := spec!{ revealSolution }
end Solidity.Examples.Benchmark.Patterns.CommitReveal
