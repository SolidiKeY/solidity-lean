// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/error/Account.sol
// Changes: comments and the require and revert messages dropped. Checked arithmetic is not
// modelled, so a uint256 parameter gets a requires >= 0.
/// @custom:key invariant balance >= 0
contract Account {
    uint256 public balance;
    uint256 public constant MAX_UINT = 2 ** 256 - 1;

    /// @custom:key requires _amount >= 0
    /// @custom:key ensures balance == \old(balance) + _amount
    function deposit(uint256 _amount) public {
        uint256 oldBalance = balance;
        uint256 newBalance = balance + _amount;

        require(newBalance >= oldBalance);

        balance = newBalance;

        assert(balance >= oldBalance);
    }

    /// @custom:key requires _amount >= 0
    /// @custom:key ensures \old(balance) >= _amount && balance == \old(balance) - _amount
    function withdraw(uint256 _amount) public {
        uint256 oldBalance = balance;

        require(balance >= _amount);

        if (balance < _amount) {
            revert();
        }

        balance -= _amount;

        assert(balance <= oldBalance);
    }
}
