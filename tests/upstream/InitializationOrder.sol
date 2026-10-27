// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.38;

contract ArgumentBase {
    uint public x = 2;
    constructor(uint) {}
    function setArgument() internal returns (uint) { x = 4; return 4; }
}
contract ArgumentOrder is ArgumentBase {
    constructor() ArgumentBase(setArgument()) {}
}

contract StageBase {
    uint public a = 42;
    uint public b;
    uint public c;
    constructor(uint value) { b = a; a = value; }
    function f(uint value) internal returns (uint) { c = value * 3; return 23; }
}
// An owner without a constructor must still get its own initialization stage.
abstract contract StageMiddle is StageBase {
    uint public middle = f(a);
}
contract StageOrder is StageMiddle {
    uint public d = f(a);
    uint public e = b;
    uint public snapshot;
    constructor() StageBase(17) { snapshot = c; c += 5; }
}
// The most derived constructor is implicit, but its initializer runs last in IR.
contract StageLeaf is StageOrder {
    uint public last = c + 1;
}

contract ReturnBase {
    uint public x = 2;
    modifier around() { x += 10; _; x += 100; }
    constructor() around() { x += 1; return; }
}
contract ReturnLeaf is ReturnBase { uint public seen = x; }

contract NarrowBase {
    uint8 public a = 255;
    constructor() { a = 1; }
}
contract NarrowLeaf is NarrowBase { uint8 public b = a + 1; }

contract FailingBase { constructor() { require(false); } }
contract FailingLeaf is FailingBase {
    uint public value = fail();
    function fail() internal pure returns (uint) { assert(false); return 0; }
}
