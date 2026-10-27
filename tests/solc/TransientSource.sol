// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

contract TransientSource layout at 42 {
    uint transient count;
    uint public saved;
    function set(uint x) external { count = x; }
    function fail() external { count = 99; saved = 99; revert(); }
    function ordinary() external {
        count = 7; saved = 3;
        assert(count == 7 && saved == 3);
        delete count;
        assert(count == 0 && saved == 3);
    }
    /// @custom:key box
    function selfSharing() external {
        count = 7;
        bool succeeded = false;
        try this.set(9) { succeeded = true; } catch {}
        assert(succeeded && count == 9);
    }
    /// @custom:key box
    function rollback() external {
        count = 7; saved = 3;
        try this.fail() {} catch {}
        assert(count == 7 && saved == 3);
    }
    function falsePersistentAlias() external {
        count = 7; saved = 3; delete count;
        assert(saved == 0);
    }
}

contract TransientBase {
    uint transient inherited;
}
contract TransientDerived is TransientBase {
    function inheritedOperations() external {
        inherited = 7;
        delete inherited;
        assert(inherited == 0);
    }
}
