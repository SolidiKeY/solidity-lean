// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract UncheckedImport {
    /// @custom:key box
    function wraps() public pure {
        uint x = 2**256 - 1;
        unchecked { x += 1; }
        assert(x == 0);
    }
    /// @custom:key box
    function falsePost() public pure {
        uint x = 2**256 - 1;
        unchecked { x += 1; }
        assert(x == 1);
    }
    /// @custom:key box
    function scopeEnds() public pure {
        uint x = 2**256 - 1;
        unchecked { x += 1; }
        x -= 1;
        assert(false);
    }
}
