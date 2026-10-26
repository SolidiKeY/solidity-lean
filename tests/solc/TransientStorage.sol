// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

// This compiles/runs in Cancun reference tests. Source admission in the Lean
// frontend must continue to refuse it until ordinary scoped integration lands.
contract TransientStorage {
    uint transient count;
    bool transient locked;
    uint public saved;

    function readCount() external view returns (uint) { return count; }
    function setCount(uint x) external { count = x; }
    function writeBoth() external { count = 7; saved = 3; }
    function readBoth() external view returns (uint, uint) { return (count, saved); }

    function reenter() external returns (uint) {
        count = 7;
        assert(this.readCount() == 7);
        this.setCount(9);
        assert(count == 9);
        return count;
    }
    function descendant() external { count = 11; saved = 9; }
    function nested(bool fail) external {
        count = 9;
        saved = 5;
        this.descendant();
        if (fail) revert();
    }
    function caught(bool fail) external returns (uint, uint) {
        count = 7;
        saved = 3;
        try this.nested(fail) {} catch {}
        assert(count == (fail ? 7 : 11));
        assert(saved == (fail ? 3 : 9));
        return (count, saved);
    }
    function staticWrite() external returns (bool) {
        count = 7;
        (bool ok,) = address(this).staticcall(abi.encodeCall(this.setCount, (9)));
        assert(!ok);
        assert(this.readCount() == 7);
        return ok;
    }
    function falseReentrantValue() external {
        count = 7;
        assert(this.readCount() == 0);
    }
    function falsePartialRollback() external {
        count = 7;
        saved = 3;
        try this.nested(true) {} catch {}
        assert(count == 11 && saved == 9);
    }
}

// Even an unused transient declaration and its generated getter cannot become
// ordinary storage silently. The child covers inherited declarations as well.
contract TransientHeader {
    uint public transient hidden;
    function ordinary() external pure { assert(true); }
}
contract InheritedTransientHeader is TransientHeader {}
contract TransientPersistentControl {
    uint public saved;
    function ordinary() external { saved = 3; assert(saved == 3); }
    function falseClaim() external { saved = 3; assert(saved == 4); }
}
