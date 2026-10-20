// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
// Internal function types: a value is its function's tag, a call through it
// a dispatch over the functions of its signature (docs/semantic-gaps.md,
// "Function types").  Calling an unassigned value is solc's Panic(0x51),
// which the model reads as a revert (box proves, diamond does not).

contract FunctionTypes {
    struct Holder { uint k; function (uint) pure returns (uint) f; }

    function (uint) pure returns (uint) op;
    Holder hold;

    function double(uint x) internal pure returns (uint) { return 2 * x; }
    function triple(uint x) internal pure returns (uint) { return 3 * x; }
    function applyTo(function (uint) pure returns (uint) h, uint x) internal pure returns (uint) {
        return h(x);
    }
    function compose(function (uint) pure returns (uint) f, function (uint) pure returns (uint) g,
            uint x) internal pure returns (uint) {
        return g(f(x));
    }
    function choose(bool b) internal pure returns (function (uint) pure returns (uint)) {
        return b ? double : triple;
    }

    function applyAndCompose() public pure {
        assert(applyTo(double, 3) == 6 && compose(double, triple, 1) == 6);
    }
    function localValue(uint8 small) public pure {
        uint x = small;
        function (uint) pure returns (uint) h = triple;
        assert(h(x) == 3 * x);
    }
    function storedByFlag(bool b) public {
        if (b) { op = double; } else { op = triple; }
        uint y = op(5);
        if (b) { assert(y == 10); } else { assert(y == 15); }
    }
    function returnedValue(uint8 small) public pure {
        uint x = small;
        function (uint) pure returns (uint) h = choose(false);
        assert(h(x) == 3 * x);
    }
    /// @custom:key box
    function unassignedPanics() public pure {
        function (uint) pure returns (uint) h;
        h(1);
        assert(false);
    }
    function memberValue(uint8 small) public {
        uint x = small;
        hold.f = double;
        function (uint) pure returns (uint) g = hold.f;
        assert(g(x) == 2 * x);
    }
    /// @custom:key box
    function deletedPanics() public {
        op = double;
        delete op;
        op(1);
        assert(false);
    }
    // not provable: an unassigned value's call does not end normally
    function unassignedDiamond() public pure {
        function (uint) pure returns (uint) h;
        h(1);
    }
    // not provable: a false postcondition
    function falsePost() public pure {
        function (uint) pure returns (uint) h = double;
        assert(h(1) == 3);
    }
    function equality() public pure {
        function (uint) pure returns (uint) h = double;
        assert(h == double && h != triple);
    }
}
