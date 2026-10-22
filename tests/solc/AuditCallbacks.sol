// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

contract AuditCallbacks {
    uint x;
    function g() external { x = 1; }

    /// @custom:key box
    function bare(address o) public {
        x = 0;
        AuditCallbacks(o).g();
        assert(x == 0);
    }

    /// @custom:key requires true
    /// @custom:key ensures x == 0
    function specified(address o) public {
        x = 0;
        AuditCallbacks(o).g();
    }

    /// @custom:key requires true
    /// @custom:key ensures true
    function specifiedTrue(address o) public { AuditCallbacks(o).g(); }
}
