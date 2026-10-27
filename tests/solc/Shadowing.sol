pragma solidity ^0.8.34;

contract ShadowingTarget {
    function value() external pure returns (uint) { return 4; }
}

contract Shadowing {
    uint public x;
    uint public constructed;

    constructor() {
        uint v = 3;
        { uint v = 5; assert(v == 5); }
        constructed = v;
        assert(constructed == 3);
    }

    modifier shadowModifier(uint v) {
        { uint v = 9; assert(v == 9); }
        assert(v == 4);
        _;
    }

    function innerReadWrite() public pure {
        uint v = 1;
        { uint v = 2; v = 3; assert(v == 3); }
        assert(v == 1);
    }

    function beforeDeclaration() public pure {
        uint v = 7;
        { v = 3; uint v; v = 4; assert(v == 4); }
        assert(v == 3);
    }

    function selfInitialization() public pure {
        uint v = 7;
        { v = 3; uint v = v; assert(v == 3); }
        assert(v == 3);
    }

    function defaultInitialization() public pure {
        uint v = 7;
        { uint v; assert(v == 0); }
        assert(v == 7);
    }

    /// @custom:key requires v == 3
    /// @custom:key ensures \result == \old(v)
    function parameterSpec(uint v) public pure returns (uint out) {
        { uint v = 8; assert(v == 8); }
        out = v;
    }

    /// @custom:key requires x == 3
    /// @custom:key ensures \result == \old(x)
    function stateParameterSpec(uint x) public pure returns (uint) {
        { uint x = 8; assert(x == 8); }
        return x;
    }

    /// @custom:key ensures out == 3
    function namedReturn() public pure returns (uint out) {
        out = 3;
        { uint out = 8; assert(out == 8); }
    }

    function stateField() public {
        x = 11;
        { uint x = 2; x = 3; assert(x == 3); }
        assert(x == 11);
    }

    function siblings() public pure {
        uint v = 1;
        { uint v = 2; assert(v == 2); }
        { uint v = 3; assert(v == 3); }
        assert(v == 1);
    }

    /// @custom:key box
    function forScope() public pure {
        uint v = 9;
        /// @custom:key invariant v <= 2
        /// @custom:key decreases (2 - v, 0)
        for (uint v = 0; v < 2; v++) { assert(v < 2); }
        assert(v == 9);
    }

    /// @custom:key box
    function loopScope() public pure {
        uint v = 2;
        {
            uint v = 1;
            /// @custom:key invariant v <= 1
            /// @custom:key invariant \forall uint v; v == v
            /// @custom:key decreases (v, 0)
            while (v > 0) { v--; }
            assert(v == 0);
        }
        assert(v == 2);
    }

    function tupleDeclaration() public pure {
        uint a = 1;
        uint b = 2;
        { (uint a, uint b) = (3, 4); assert(a == 3 && b == 4); }
        assert(a == 1 && b == 2);
    }

    function modified() public pure shadowModifier(4) {
        uint v = 1;
        { uint v = 2; assert(v == 2); }
        assert(v == 1);
    }

    /// @custom:key box
    function catchScope(address target) public {
        uint v = 9;
        try ShadowingTarget(target).value() returns (uint v) {
            { uint v = 2; assert(v == 2); }
        } catch Error(string memory v) {
            // A catch binding has its own type and lifetime.
            { uint v = 3; assert(v == 3); }
        } catch { }
        assert(v == 9);
    }

    /// @custom:key box
    function legacyAliases(uint x, uint x_, uint from, uint from_) public pure {
        require(x == 1 && x_ == 2 && from == 3 && from_ == 4);
        { uint x = 5; uint from = 6; assert(x == 5 && from == 6); }
        assert(x == 1 && x_ == 2 && from == 3 && from_ == 4);
    }

    function originalFormalNames(uint v, uint v_) internal pure returns (uint) {
        { uint v = 7; assert(v == 7); }
        return v * 10 + v_;
    }

    function namedCall() public pure {
        assert(originalFormalNames({v_: 2, v: 1}) == 12);
    }

    /// @custom:key requires v == 2
    /// @custom:key ensures false
    function witness(uint v, uint v_) public pure {
        { uint v = 7; assert(v == 7); }
    }

    function falseAssertion() public pure {
        uint v = 1;
        { uint v = 2; assert(v == 2); }
        assert(v == 2);
    }
}
