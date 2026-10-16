// Source: https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/first-app/Counter.sol
// Unmodified; only @custom:key clauses are added.
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract Counter {
    uint256 public count;

    // Function to get the current count
    function get() public view returns (uint256) {
        return count;
    }

    // Function to increment count by 1
    /// @custom:key ensures count == \old(count) + 1
    function inc() public {
        count += 1;
    }

    // Function to decrement count by 1
    /// @custom:key requires count >= 1
    /// @custom:key ensures count == \old(count) - 1
    function dec() public {
        // This function will fail if count = 0
        count -= 1;
    }
}
