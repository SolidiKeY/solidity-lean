// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.7.0 <0.9.0;

// Source: https://github.com/ethereum/solidity/blob/0944010b9e19e8717b7d40dd4a22a8586713631b/docs/examples/voting.rst
// Changes: comments and require messages dropped (string literals fail to load). Proposal names are
// uint256 instead of bytes32, since a bytes32 variable fails to load. The constructor pushes an
// empty Proposal and assigns its fields (a struct constructor fails to load) and copies
// proposalNames to a local first (indexing a memory-array parameter fails to load); it is skipped,
// since a memory-array parameter has no .key sort. A storage read on the right of += is bound to
// a local first. The two loops carry @custom:key invariants.
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

    /// @custom:key ensures \old(chairperson) == msg.sender && chairperson == \old(chairperson)
    /// @custom:key ensures \old(voters[voter].voted) == false && \old(voters[voter].weight) == 0
    /// @custom:key ensures voters[voter].weight == 1 && voters[voter].voted == false
    function giveRightToVote(address voter) external {
        require(msg.sender == chairperson);
        require(!voters[voter].voted);
        require(voters[voter].weight == 0);
        voters[voter].weight = 1;
    }

    /// @custom:key ensures \old(voters[msg.sender].weight) != 0 && \old(voters[msg.sender].voted) == false
    /// @custom:key ensures voters[msg.sender].voted == true && voters[msg.sender].delegate != msg.sender
    /// @custom:key ensures voters[voters[msg.sender].delegate].delegate == address(0)
    /// @custom:key ensures \forall address d; d == voters[msg.sender].delegate && \old(voters[d].voted) == false
    ///     -> voters[d].weight == \old(voters[d].weight) + \old(voters[msg.sender].weight)
    /// @custom:key ensures \forall address d; \forall uint v; d == voters[msg.sender].delegate && \old(voters[d].voted) == true && v == voters[d].vote
    ///     -> proposals[v].voteCount == \old(proposals[v].voteCount) + \old(voters[msg.sender].weight)
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

    /// @custom:key requires proposal >= 0
    /// @custom:key ensures \old(voters[msg.sender].weight) != 0 && \old(voters[msg.sender].voted) == false
    /// @custom:key ensures voters[msg.sender].voted == true && voters[msg.sender].vote == proposal
    /// @custom:key ensures proposals[proposal].voteCount == \old(proposals[proposal].voteCount) + \old(voters[msg.sender].weight)
    function vote(uint proposal) external {
        Voter storage sender = voters[msg.sender];
        require(sender.weight != 0);
        require(!sender.voted);
        sender.voted = true;
        sender.vote = proposal;

        uint w = sender.weight;
        proposals[proposal].voteCount += w;
    }

    /// @custom:key ensures winningProposal_ == 0 || winningProposal_ < proposals.length
    /// @custom:key ensures \forall uint i; 0 <= i && i < proposals.length -> proposals[i].voteCount <= proposals[winningProposal_].voteCount
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

    /// @custom:key ensures \exists uint i; 0 <= i && i < proposals.length && winnerName_ == proposals[i].name
    /// @custom:key ensures \forall uint i; 0 <= i && i < proposals.length
    ///     -> (\exists uint w; 0 <= w && w < proposals.length && winnerName_ == proposals[w].name && proposals[i].voteCount <= proposals[w].voteCount)
    function winnerName() external view
            returns (uint256 winnerName_)
    {
        winnerName_ = proposals[winningProposal()].name;
    }
}
