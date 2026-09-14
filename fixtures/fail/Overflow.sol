// SPDX-License-Identifier: MIT
pragma solidity 0.8.33;

contract Overflow {
    function unsafeAdd(uint8 x) public pure returns (uint8) {
        return x + 1;
    }
}
