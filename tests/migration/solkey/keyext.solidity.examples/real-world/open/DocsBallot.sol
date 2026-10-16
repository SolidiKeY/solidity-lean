// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.7.0 <0.9.0;

// Source: https://github.com/ethereum/solidity/blob/0944010b9e19e8717b7d40dd4a22a8586713631b/docs/examples/voting.rst
// Changes: as in ../DocsBallot.sol, of which this keeps winningProposal and winnerName.
/// @custom:key invariant \forall address a; voters[a].weight >= 0
/// @custom:key invariant \forall uint i; 0 <= i && i < proposals.length -> proposals[i].voteCount >= 0
contract DocsBallot {
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

    /// @custom:key skip
    function winningProposal() public view
            returns (uint winningProposal_)
    {
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

    // open: the witness w is winningProposal()'s result; automation does not instantiate the existential with it
    /// @custom:key ensures \exists uint w; 0 <= w && w < proposals.length && winnerName_ == proposals[w].name
    ///     && (\forall uint i; 0 <= i && i < proposals.length -> proposals[i].voteCount <= proposals[w].voteCount)
    function winnerName() external view
            returns (uint256 winnerName_)
    {
        winnerName_ = proposals[winningProposal()].name;
    }
}
