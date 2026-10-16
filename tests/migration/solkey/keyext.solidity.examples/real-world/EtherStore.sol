// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/hacks/re-entrancy/ReEntrancy.sol
// Changes: comments, the require message, the Attack contract and getBalance
// (address(this).balance) dropped. The invariant ties each balance to the payment ledger; it
// is proved under the default transfer semantics, while under
// -O transferSemantics:withCallback withdraw stays open, since the external call is made
// before balances[msg.sender] is zeroed: the re-entrancy bug.
/// @custom:key invariant \forall address a; balances[a] >= 0 && balances[a] == net(a)
contract EtherStore {
    mapping(address => uint256) public balances;

    /// @custom:key ensures balances[msg.sender] == \old(balances[msg.sender]) + msg.value
    function deposit() public payable {
        balances[msg.sender] += msg.value;
    }

    /// @custom:key ensures \old(balances[msg.sender]) > 0 && balances[msg.sender] == 0
    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) - \old(balances[msg.sender])
    function withdraw() public {
        uint256 bal = balances[msg.sender];
        require(bal > 0);

        (bool sent,) = msg.sender.call{value: bal}("");
        require(sent);

        balances[msg.sender] = 0;
    }
}
