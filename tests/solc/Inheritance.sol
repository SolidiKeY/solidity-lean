// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Ancestor {
    enum Phase { Open, Closed }
    struct FileLevelPair { uint left; uint right; }
    FileLevelPair pair;
    uint shared;
    function pick() internal pure virtual returns (uint) { return 1; }
    function viaBase() internal pure returns (uint) { return pick(); }
    function ordered(uint a, uint b) internal pure virtual returns (uint) { return a + 2 * b; }
    function viaNamed() internal pure returns (uint) { return ordered({b: 3, a: 2}); }
    function secret() private pure returns (uint) { return 7; }
    function viaPrivate() internal pure returns (uint) { return secret(); }
    modifier around() virtual { shared = 1; _; shared += 1; }
    modifier countPhase() {
        uint i = 0;
        /// @custom:key invariant i <= Phase.Closed
        while (i < 1) { i++; }
        assert(i == 1);
        _;
    }
    function viaMod() internal around returns (uint) { return shared; }
}

contract Inherited is Ancestor {
    function pick() internal pure override returns (uint) { return 2; }
    function ordered(uint b, uint a) internal pure override returns (uint) { return 10 * b + a; }
    modifier around() override { shared = 5; _; shared += 1; }
    function dispatch() public pure { uint r = viaBase(); assert(r == 2); }
    function staticCall() public pure { uint r = Ancestor.pick(); assert(r == 1); }
    function staticStillDispatches() public pure { uint r = Ancestor.viaBase(); assert(r == 2); }
    function namedCall() public pure { uint r = viaNamed(); assert(r == 23); }
    function privateCall() public pure { uint r = viaPrivate(); assert(r == 7); }
    function modified() public { uint r = viaMod(); assert(r == 5); assert(shared == 6); }
    function staticModifier() public Ancestor.around { assert(shared == 1); }
    function inheritedStruct() public { pair.left = 3; assert(pair.left == 3); }
    /// @custom:key ensures Phase.Closed == 1
    function inheritedEnumSpec() public pure {}
    /// @custom:key ensures Phase.Closed == 0
    function falseInheritedEnumSpec() public pure {}
    /// @custom:key box
    function inheritedEnumModifier() public countPhase {}
    function falseDispatch() public pure { uint r = viaBase(); assert(r == 1); }
    function externalValue() public pure returns (uint) { return 2; }
    /// @custom:key box
    function externalStaysExternal() public {
        try this.externalValue() returns (uint r) { assert(r == 2); } catch {}
    }
    function superCall() public pure { uint r = super.pick(); assert(r == 1); }
    function superNamed() public pure { uint r = super.ordered({a: 1, b: 4}); assert(r == 9); }
    function falseSuper() public pure { uint r = super.pick(); assert(r == 2); }
}

// `super` follows the most-derived C3 order [SuperDiamond, SuperRight,
// SuperLeft, SuperRoot]: SuperRight's `super` is SuperLeft, not its parent.
contract SuperRoot { function name() internal pure virtual returns (uint) { return 1; } }
contract SuperLeft is SuperRoot {
    function name() internal pure virtual override returns (uint) { return super.name() * 10 + 2; }
}
contract SuperRight is SuperRoot {
    function name() internal pure virtual override returns (uint) { return super.name() * 10 + 3; }
}
contract SuperDiamond is SuperLeft, SuperRight {
    function name() internal pure override(SuperLeft, SuperRight) returns (uint) {
        return super.name() * 10 + 4;
    }
    function diamondSuper() public pure { assert(name() == 1234); }
    function staticRight() public pure { assert(SuperRight.name() == 123); }
    function falseDiamondSuper() public pure { assert(name() == 134); }
}

// solc's legacy creation code: every initializer (most base first), then the
// base constructors' arguments (derived to base), then the bodies (base to
// derived). `late` is initialized before `CtorMid` passes it on, and the base
// constructor already dispatches `probe` to `CtorLeaf` and reads `leaf`.
contract CtorRoot {
    uint root;
    uint seen;
    uint early = 7;
    constructor(uint a) { seen = probe() + early; root = a; }
    function probe() internal view virtual returns (uint) { return 0; }
}
contract CtorMid is CtorRoot {
    uint mid;
    uint late = 9;
    constructor(uint m) CtorRoot(m + late) { mid = root * 2 + m; }
}
contract CtorLeaf is CtorMid(3) {
    uint leaf = 11;
    uint order;
    function probe() internal view override returns (uint) { return leaf * 100; }
    constructor() {
        order = mid * 100 + leaf;
        assert(root == 12); assert(seen == 1107); assert(mid == 27); assert(order == 2711);
    }
}
contract CtorFalse is CtorMid(3) {
    constructor() { assert(root == 3); }
}
contract CtorImplicit is CtorRoot(4) { uint next = root + 1; }
contract CtorUnnamed { uint got; constructor(uint, uint b) { got = b; } }
contract CtorUnnamedChild is CtorUnnamed {
    constructor(uint x) CtorUnnamed(x, x) payable { assert(got == x); }
}

// A base contract's invariant is the derived contract's too, with its own.
/// @custom:key invariant guarded <= 10
contract Guarded { uint guarded; }
/// @custom:key invariant guarded >= 1
contract GuardedChild is Guarded {
    function bump() public { if (guarded < 10) { guarded += 1; } }
    function breaksBase() public { guarded = 11; }
    function breaksOwn() public { guarded = 0; }
}

contract InitRoot {
    uint counter;
    uint initialized = setup();
    function setup() internal virtual returns (uint) { counter += 1; return counter; }
}
contract InitLeft is InitRoot { uint left = counter + 1; }
contract InitRight is InitRoot { uint right = counter + 2; }
contract InitDiamond is InitLeft, InitRight {
    uint result = left * 10 + right;
    function setup() internal override returns (uint) { counter += 2; return counter; }
    constructor() {
        assert(counter == 2); assert(initialized == 2);
        assert(left == 3); assert(right == 4); assert(result == 34);
    }
}
