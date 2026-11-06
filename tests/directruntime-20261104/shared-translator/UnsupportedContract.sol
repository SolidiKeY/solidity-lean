// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
contract UnsupportedContract {
    struct UnsupportedSibling { uint256 value; }
    function supported() public pure { assert(true); }
}
