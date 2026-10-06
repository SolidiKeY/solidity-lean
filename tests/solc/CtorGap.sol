// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// A declared constructor the import leaves out (a modifier on it): the
// initializer goes with it, since the implicit constructor would run it alone.
contract CtorGap {
    uint limit = 5;
    uint count;

    modifier positive(uint x) {
        require(x > 0);
        _;
    }

    constructor(uint start) positive(start) {
        count = start;
    }

    function get() public view returns (uint) {
        return count;
    }
}
