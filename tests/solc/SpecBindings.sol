// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract SpecBindings {
    uint value;
    uint value_;
    uint age;
    mapping(uint => uint) rows;
    struct Token { uint value; }
    struct Account { uint balance; Token token; }
    struct Person { Account account; uint age; }
    Person alice;

    modifier loopGuard(uint from) {
        uint i = 0;
        /// @custom:key invariant from == 7 && i <= 1
        /// @custom:key decreases 1 - i
        while (i < 1) { i++; }
        _;
    }

    /// @custom:key requires from == 7 && to == 9
    /// @custom:key ensures from + to == 16
    function keywords(uint from, uint to) public pure {}

    /// @custom:key requires from == 7
    /// @custom:key ensures \old(from) == from
    function oldParameter(uint from) public pure {}

    /// @custom:key requires value == 7
    /// @custom:key ensures value == 7
    function stateShadow(uint value) public pure {}

    /// @custom:key requires value == 7
    /// @custom:key ensures value == 0
    function falseStateShadow(uint value) public pure {}

    /// @custom:key requires value == 7 && value_ == 9
    /// @custom:key ensures false
    function falseDistinctParameters(uint value, uint value_) public pure {}

    /// @custom:key requires value == 7 && value_ == 9
    /// @custom:key ensures value + value_ == 16
    function distinctParameters(uint value, uint value_) public pure {}

    /// @custom:key ensures \result == from && from == x
    function namedReturn(uint x) public pure returns (uint from) { from = x; }

    /// @custom:key requires age == 0
    /// @custom:key ensures \old(age) == 0 && age == 7
    function returnScope() public view returns (uint age) { age = 7; }

    /// @custom:key requires age == 0
    /// @custom:key ensures \old(age) == 7
    function falseOldReturnScope() public view returns (uint age) { age = 7; }

    /// @custom:key requires from == 7
    /// @custom:key ensures \forall uint from; from == 7
    function falseQuantifiedShadow(uint from) public pure {}

    /// @custom:key requires from == 0
    /// @custom:key ensures \exists uint from; from == 1
    function existentialShadow(uint from) public pure {}

    /// @custom:key requires from == 7
    /// @custom:key ensures (\forall uint from; from == from) && from == 7
    function quantifiedSibling(uint from) public pure {}

    /// @custom:key requires from == 7
    /// @custom:key ensures (\forall uint from; from == from) && from == 0
    function falseQuantifiedSibling(uint from) public pure {}

    /// @custom:key requires from == 1
    /// @custom:key ensures \forall uint from_; from == 1
    function avoidCapture(uint from) public pure {}

    /// @custom:key requires from == 0
    /// @custom:key ensures \forall uint from_; from == from_
    function falseCapture(uint from) public pure {}

    /// @custom:key requires from == 0
    /// @custom:key ensures \forall uint from_; \forall uint from__; \forall uint from___; \forall uint from____; \forall uint from_____; \forall uint from______; \forall uint from_______; \forall uint from________; \forall uint from_________; from == from_________
    function falseDeepCapture(uint from) public pure {}

    /// @custom:key ensures alice.age == \old(alice.age)
    function memberLabel(uint age) public view {}

    /// @custom:key ensures (alice).age == \old((alice).age)
    function splitMemberLabel(uint age) public view {}

    /// @custom:key requires from == 7
    /// @custom:key ensures rows[from] == 1
    /// @custom:key assignable rows[from]
    function assignableIndex(uint from) public { rows[from] = 1; }

    /// @custom:key requires from == 7
    /// @custom:key ensures true
    /// @custom:key assignable rows[from]
    function falseFrame(uint from) public { rows[8] = 1; }

    /// @custom:key ensures true
    function bodyLocal() public pure { uint from = 1; assert(from == 1); }

    /// @custom:key requires «from» == 7
    /// @custom:key ensures «from» == 7
    function escaped(uint from) public pure {}

    /// @custom:key requires from /- « ignored /- from -/ » -/ == 7
    /// @custom:key ensures from == 7
    function comments(uint from) public pure {}

    /// @custom:key requires age == 7
    /// @custom:key ensures age == 7
    function parameterLoop(uint age) public pure {
        uint i = 0;
        /// @custom:key invariant age == 7 && i <= 1
        /// @custom:key decreases 1 - i
        while (i < 1) { i++; }
    }

    /// @custom:key ensures \result == 7
    function localLoop() public pure returns (uint) {
        uint from = 7;
        uint i = 0;
        /// @custom:key invariant from == 7 && i <= 1
        /// @custom:key decreases 1 - i
        while (i < 1) { i++; }
        return from;
    }

    /// @custom:key requires age == 0
    /// @custom:key ensures age == 0
    function loopScopeExit() public view {
        /// @custom:key invariant age <= 1
        /// @custom:key decreases 1 - age
        for (uint age = 0; age < 1; age++) {}
        /// @custom:key invariant age == 0
        /// @custom:key decreases 0
        while (false) {}
    }

    /// @custom:key requires age == 0
    /// @custom:key ensures age == 0
    function blockScopeExit() public view {
        {
            uint age = 7;
            uint i = 0;
            /// @custom:key invariant age == 7 && i <= 1
            /// @custom:key decreases 1 - i
            while (i < 1) { i++; }
        }
        /// @custom:key invariant age == 0
        /// @custom:key decreases 0
        while (false) {}
    }

    /// @custom:key ensures age == 7
    function returnLoop() public pure returns (uint age) {
        age = 7;
        uint i = 0;
        /// @custom:key invariant age == 7 && i <= 1
        /// @custom:key decreases 1 - i
        while (i < 1) { i++; }
    }

    /// @custom:key ensures true
    function modifierLoop() public pure loopGuard(7) {}

    /// @custom:key requires from == 7
    /// @custom:key ensures true
    function unknownLoopName(uint from) public pure {
        /// @custom:key invariant from_ == 7
        /// @custom:key decreases 0
        while (false) {}
    }

    function externalValue() external pure returns (uint) { return 2; }

    /// @custom:key requires age == 0
    /// @custom:key ensures age == 0
    function tryScopeExit() public view {
        try this.externalValue() returns (uint age) {
            uint i = 0;
            /// @custom:key invariant age >= 0 && i <= 1
            /// @custom:key decreases 1 - i
            while (i < 1) { i++; }
        } catch Panic(uint age) {
            uint i = 0;
            /// @custom:key invariant age >= 0 && i <= 1
            /// @custom:key decreases 1 - i
            while (i < 1) { i++; }
        } catch {}
        /// @custom:key invariant age == 0
        /// @custom:key decreases 0
        while (false) {}
    }

    /// @custom:key requires from == 7
    /// @custom:key ensures false; requires false
    function malformedRenamed(uint from) public pure { assert(false); }

    function stillChecked() public pure { assert(false); }
}

contract SpecBindingConstructor {
    uint marker = 1;
    /// @custom:key requires from == 7
    /// @custom:key ensures marker == from
    constructor(uint from) { marker = from; }
}

contract SpecBindingBase {
    /// @custom:key ensures \result == from
    function identity(uint from) internal pure returns (uint) { return from; }
}

contract SpecBindingInherited is SpecBindingBase {
    /// @custom:key requires from == 7
    /// @custom:key ensures \result == 7
    function inheritedHelper(uint from) public pure returns (uint) { return identity(from); }
}
