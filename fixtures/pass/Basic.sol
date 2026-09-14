// SPDX-License-Identifier: MIT
pragma solidity 0.8.33;

contract Basic {
    uint8 public value;

    constructor(uint8 start) {
        value = start;
    }

    function safe(uint8 x) public returns (uint8) {
        require(x < 255);
        uint8 y = x + 1;
        assert(y > x);
        value = y;
        return y;
    }

    function shortCircuit(uint8 x) external {
        require(x == 0 || 10 / x > 0);
    }
}
