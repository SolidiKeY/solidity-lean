// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Examples the calculus cannot prove, kept out of every scanned example directory.
///
/// Each function reverts on a real EVM (solc >= 0.8 checked arithmetic, Panic 0x11) before
/// reaching its `assert(false)`. SolKey models integers as unbounded mathematical integers, so
/// the overflowing operation succeeds in the calculus, the revert path does not exist, and the
/// `assert(false)` is reachable — the obligation is unprovable even under the box modality.
/// No test suite scans this directory; the functions stay valid Solidity so they can be
/// compiled and executed if a bounded-integer semantics is ever reintroduced.
contract Unprovable {
    struct Person { uint age; }

    uint total;
    uint age;
    Person alice;
    mapping(uint => uint) balances;

    /// @custom:key box
    function checkedLocalOverflowReverts() public pure {
        uint8 x;
        x = 250;
        x += 10;
        assert(false);
    }

    /// @custom:key box
    function checkedStorageUnderflowReverts() public {
        require(total == 0);
        total -= 1;
        assert(false);
    }

    /// @custom:key box
    function checkedStorageDecrementUnderflowReverts() public {
        require(age == 0);
        --age;
        assert(false);
    }

    /// @custom:key box
    function checkedFieldDecrementUnderflowReverts() public {
        require(alice.age == 0);
        alice.age--;
        assert(false);
    }

    /// @custom:key box
    function checkedMappingEntryDecrementUnderflowReverts() public {
        require(balances[1] == 0);
        balances[1]--;
        assert(false);
    }

    /// @custom:key box
    function checkedPowerOverflowReverts() public pure {
        uint8 b;
        uint8 r;
        b = 16;
        r = b ** 2;
        assert(false);
    }

    /// @custom:key box
    function checkedDivisionOverflowReverts() public pure {
        int8 x;
        int8 mone;
        int8 r;
        x = -127;
        x -= 1;
        mone = -1;
        r = x / mone;
        assert(false);
    }

    /// @custom:key box
    function checkedUnaryMinusMinReverts() public pure {
        int8 m;
        int8 r;
        m = -127;
        m -= 1;
        r = -m;
        assert(false);
    }
}
