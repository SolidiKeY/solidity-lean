// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SolcHigherLevelOpenBaseBase {
    uint x;

    function bg() internal pure virtual returns (uint256 r) {
        return 1;
    }

    function init(uint a, uint b) internal virtual {
        x = a;
    }

    function nf(uint256 a, uint256 b, uint256 c) internal pure virtual returns (uint256) {
        return 1 * a + 2 * b + 3 * c;
    }

    function vf() internal pure returns (uint256 i) {
        return vg();
    }

    function vg() internal pure virtual returns (uint256 i) {
        return 1;
    }

    function ivf() internal pure returns (uint256 i) {
        return ivg();
    }

    function ivg() internal pure virtual returns (uint256 i) {
        return 1;
    }
}

contract SolcHigherLevelOpenBase is SolcHigherLevelOpenBaseBase {
    function bg() internal pure virtual override returns (uint256 r) {
        return 2;
    }

    function init(uint a, uint b) internal override {
    }
}

contract SolcHigherLevelOpen is SolcHigherLevelOpenBase {
    function bg() internal pure override returns (uint256 r) {
        return 3;
    }

    function nf(uint256 b, uint256 a, uint256 c) internal pure override returns (uint256) {
        return 2 * b + 3 * a + 4 * c;
    }

    function vg() internal pure override returns (uint256 i) {
        return 2;
    }

    function ivg() internal pure override returns (uint256 i) {
        return 2;
    }

    /// solc: semanticTests/inheritance/explicit_base_class.sol
    // open: a base-qualified call BaseBase.g() is lowered to address.g() and has no rule
    function explicitBaseClass() public pure {
        uint256 g = bg();
        uint256 f = SolcHigherLevelOpenBaseBase.bg();
        assert(g == 3);
        assert(f == 1);
    }

    /// solc: semanticTests/inheritance/inherited_function.sol
    // open: a base-qualified call A.f() is lowered to address.f() and has no rule
    function inheritedFunction() public pure {
        uint256 r = SolcHigherLevelOpenBase.bg();
        assert(r == 2);
    }

    /// solc: semanticTests/inheritance/inherited_function_named_parameters.sol
    // open: a base-qualified call A.f(...) is lowered to address.f(...) and has no rule
    function inheritedNamedBaseOrdered() public pure {
        uint256 r = SolcHigherLevelOpenBaseBase.nf({a: 1, b: 2, c: 3});
        assert(r == 14);
    }

    /// solc: smtCheckerTests/inheritance/overridden_function_static_call_parent.sol
    // open: a base-qualified call BaseBase.init(c, d) is lowered to address.init(c, d) and has no rule
    /// @custom:key box
    function overriddenFunctionStaticCallParent(uint c, uint d) public {
        require(c == 1 && d == 0);
        SolcHigherLevelOpenBaseBase.init(c, d);
        uint r = x;
        assert(r == c);
    }
}
