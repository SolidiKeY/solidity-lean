// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract MinimalAssert {
    uint age;
    function testSimpleAssert() public {
        age = 42;
        uint v = age;
        assert(v == 42);
    }
}
