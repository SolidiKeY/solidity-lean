// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// An implicit constructor whose initializer calls a function the import
// leaves out (a modifier on it): the initializer is left out, with a warning.
contract InitGap {
    uint limit = cap();
    uint count;

    modifier always() {
        _;
    }

    function cap() internal pure always returns (uint) {
        return 5;
    }

    function get() public view returns (uint) {
        return count;
    }
}
