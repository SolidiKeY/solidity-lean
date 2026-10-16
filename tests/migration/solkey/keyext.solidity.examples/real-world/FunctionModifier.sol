// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/function-modifier/FunctionModifier.sol
// Changes: comments and require messages dropped. Checked arithmetic is not modelled, so
// decrement requires i <= x (the case in which x -= i does not revert); its ensures i <= 1
// proves that the guarded recursive call always reverts.
contract FunctionModifier {
    address public owner;
    uint256 public x = 10;
    bool public locked;

    /// @custom:key ensures owner == msg.sender && x == 10 && !locked
    constructor() {
        owner = msg.sender;
    }

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    modifier validAddress(address _addr) {
        require(_addr != address(0));
        _;
    }

    /// @custom:key ensures \old(owner) == msg.sender && _newOwner != address(0)
    /// @custom:key ensures owner == _newOwner && x == \old(x) && locked == \old(locked)
    function changeOwner(address _newOwner)
        public
        onlyOwner
        validAddress(_newOwner)
    {
        owner = _newOwner;
    }

    modifier noReentrancy() {
        require(!locked);

        locked = true;
        _;
        locked = false;
    }

    /// @custom:key requires i >= 0 && i <= x
    /// @custom:key ensures !\old(locked) && i <= 1 && x == \old(x) - i && !locked && owner == \old(owner)
    function decrement(uint256 i) public noReentrancy {
        x -= i;

        if (i > 1) {
            decrement(i - 1);
        }
    }
}
