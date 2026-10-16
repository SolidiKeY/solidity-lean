// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/hacks/overflow/Overflow.sol
// Changes: comments, require messages and the Attack contract dropped; ported from 0.7.6 to
// 0.8, so lockTime can no longer overflow; block.timestamp is the timeNow state variable, since
// block.timestamp fails to load (NullPointerException) and the spec language has no block.
// Checked arithmetic is not modelled, so a uint256 parameter gets a requires >= 0.
/// @custom:key invariant timeNow >= 0
/// @custom:key invariant \forall address a; balances[a] >= 0 && lockTime[a] >= 0
contract TimeLock {
    mapping(address => uint256) public balances;
    mapping(address => uint256) public lockTime;
    uint256 timeNow;

    /// @custom:key ensures balances[msg.sender] == \old(balances[msg.sender]) + msg.value
    /// @custom:key ensures lockTime[msg.sender] == timeNow + 604800
    function deposit() external payable {
        balances[msg.sender] += msg.value;
        lockTime[msg.sender] = timeNow + 1 weeks;
    }

    /// @custom:key requires _secondsToIncrease >= 0
    /// @custom:key ensures lockTime[msg.sender] == \old(lockTime[msg.sender]) + _secondsToIncrease
    /// @custom:key ensures balances[msg.sender] == \old(balances[msg.sender])
    function increaseLockTime(uint256 _secondsToIncrease) public {
        lockTime[msg.sender] += _secondsToIncrease;
    }

    /// @custom:key ensures \old(balances[msg.sender]) > 0 && timeNow > \old(lockTime[msg.sender]) && balances[msg.sender] == 0
    /// @custom:key ensures lockTime[msg.sender] == \old(lockTime[msg.sender])
    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) - \old(balances[msg.sender])
    function withdraw() public {
        require(balances[msg.sender] > 0);
        require(timeNow > lockTime[msg.sender]);

        uint256 amount = balances[msg.sender];
        balances[msg.sender] = 0;

        (bool sent,) = msg.sender.call{value: amount}("");
        require(sent);
    }
}
