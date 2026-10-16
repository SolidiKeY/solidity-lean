// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/first-app/Counter.sol
// Changes: comments dropped; get's return value is named c. Checked arithmetic is not
// modelled, so dec requires count >= 1, the case in which count -= 1 does not revert.
/// @custom:key invariant count >= 0
contract Counter {
    uint256 public count;

    /// @custom:key ensures c == count && count == \old(count)
    function get() public view returns (uint256 c) {
        return count;
    }

    /// @custom:key ensures count == \old(count) + 1
    function inc() public {
        count += 1;
    }

    /// @custom:key requires count >= 1
    /// @custom:key ensures count == \old(count) - 1
    function dec() public {
        count -= 1;
    }
}
