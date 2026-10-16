// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

contract StorageReturns {
    uint[] values;
    uint[] other;
    uint[][] rows;
    uint calls;

    function valuesRef() internal returns (uint[] storage r) {
        calls++;
        r = values;
    }

    function otherRef() internal returns (uint[] storage r) {
        calls++;
        r = other;
    }

    function rowRef(uint i) internal view returns (uint[] storage) {
        return rows[i];
    }

    function allocatedRef() internal returns (uint[] storage r) {
        uint[] memory tmp = new uint[](1);
        tmp[0] = 41;
        values.push(tmp[0]);
        r = values;
    }

    function rejectedRef() internal view returns (uint[] storage r) {
        require(false);
        r = values;
    }

    /// @custom:key box
    function bindsRoot() public {
        delete values; calls = 0;
        uint[] storage p = valuesRef();
        p.push(7);
        assert(calls == 1 && values.length == 1 && values[0] == 7);
    }

    /// @custom:key box
    function rebinds() public {
        delete values; delete other; calls = 0;
        uint[] storage p = valuesRef();
        p = otherRef();
        p.push(11);
        assert(calls == 2 && values.length == 0 && other.length == 1 && other[0] == 11);
    }

    /// @custom:key box
    function returnsIndexed() public {
        delete rows;
        rows.push(); rows.push();
        uint i = 0;
        uint[] storage p = rowRef(i + 1);
        p.push(17);
        assert(rows[0].length == 0 && rows[1].length == 1 && rows[1][0] == 17);
    }

    /// @custom:key box
    function heapGrowth() public {
        delete values;
        uint[] memory beforeCall = new uint[](1);
        beforeCall[0] = 19;
        uint[] storage p = allocatedRef();
        beforeCall[0] = 23;
        p.push(beforeCall[0]);
        assert(values.length == 2 && values[0] == 41 && values[1] == 23);
    }

    /// @custom:key box
    function calleeReverts() public {
        uint[] storage p = rejectedRef();
        p.push(29);
        assert(false);
    }

    /// @custom:key box
    function falseCopy() public {
        delete values;
        uint[] storage p = valuesRef();
        p.push(31);
        assert(values.length == 0);
    }

    /// @custom:key box
    function receiverPush() public {
        delete values; calls = 0;
        valuesRef().push();
        assert(calls == 1 && values.length == 1);
    }

    /// @custom:key box
    function receiverPushValue() public {
        delete values; calls = 0;
        valuesRef().push(37);
        assert(calls == 1 && values[0] == 37);
    }

    /// @custom:key box
    function receiverPop() public {
        delete values; calls = 0;
        values.push(43);
        valuesRef().pop();
        assert(calls == 1 && values.length == 0);
    }

    /// @custom:key box
    function receiverReadsAfterGetter() public {
        delete values; calls = 0;
        valuesRef().push(calls);
        assert(calls == 1 && values[0] == 1);
    }

    /// @custom:key box
    function receiverReadsBeforeGetterFalse() public {
        delete values; calls = 0;
        valuesRef().push(calls);
        assert(values[0] == 0);
    }

    /// @custom:key box
    function receiverEffectfulOperand() public {
        delete values; calls = 0;
        valuesRef().push(calls++);
        assert(calls == 2 && values[0] == 1);
    }
}
