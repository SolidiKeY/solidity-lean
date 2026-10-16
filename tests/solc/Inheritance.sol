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
    function superRemainsUnsupported() public pure { uint r = super.pick(); assert(r == 1); }
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
