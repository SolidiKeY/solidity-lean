// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

interface SolcHigherLevelParent {
    function parentFun() external returns (uint256);
}

contract SolcHigherLevelRoot {
    uint256 x;
    uint constant K = 7;
}

contract SolcHigherLevelA is SolcHigherLevelRoot {
    uint256 dataBase;
    uint256 z;
    uint256 private t;

    function getViaBase() internal view returns (uint256 i) {
        return dataBase;
    }

    function ovDirect() internal pure returns (uint256) {
        return 10;
    }

    function ovIndirect(uint256 a) internal pure returns (uint256) {
        return 2 * a;
    }

    function vg() internal pure virtual returns (uint256 i) {
        return 1;
    }

    function vf() internal pure returns (uint256 i) {
        return vg();
    }

    function ivf() internal pure returns (uint256 i) {
        return ivg();
    }

    function ivg() internal pure virtual returns (uint256 i) {
        return 1;
    }

    function nf(uint256 a, uint256 b, uint256 c) internal pure virtual returns (uint256) {
        return 1 * a + 2 * b + 3 * c;
    }

    function mutability() internal virtual {
        mutableWithViewOverride();
        mutableWithPureOverride();
        viewWithPureOverride();
    }

    function mutableWithViewOverride() internal virtual {}

    function mutableWithPureOverride() internal virtual {}

    function viewWithPureOverride() internal view virtual {}
}

contract SolcHigherLevelB {
    function ovIndirect() internal pure returns (uint256) {
        return 10;
    }
}

/// Ports of the solc compiler tests above the core fragment:
/// `semanticTests/inheritance/`, `virtualFunctions/`, `getters/` and
/// `smtCheckerTests/inheritance/`.
contract SolcHigherLevel is SolcHigherLevelA, SolcHigherLevelB, SolcHigherLevelParent {
    struct Y {
        uint a;
        uint b;
    }

    struct S {
        uint a;
        uint b;
        uint c;
        uint d;
    }

    uint256 dataDerived;
    uint256 private zp;
    uint public pa;
    uint public pb;
    uint public pc;
    uint public pd;
    bool public ph;
    mapping(uint => mapping(uint => uint)) public gx;
    mapping(uint a => mapping(uint b => uint c)) public named;
    mapping(uint => mapping(uint => S)) public gs;
    mapping(uint256 => Y[]) public gm;
    mapping(uint256 => Y[3]) public gn;
    mapping(uint256 => Y)[] public gam;
    mapping(uint256 => Y)[3] public gan;
    uint[][2] public ga;

    function setData(uint256 base, uint256 derived) internal returns (bool r) {
        dataBase = base;
        dataDerived = derived;
        return true;
    }

    function getViaDerived() internal view returns (uint256 base, uint256 derived) {
        base = dataBase;
        derived = dataDerived;
    }

    function ovDirect(uint256 i) internal pure returns (uint256) {
        return 2 * i;
    }

    function vg() internal pure override returns (uint256 i) {
        return 2;
    }

    function ivg() internal pure override returns (uint256 i) {
        return 2;
    }

    function nf(uint256 b, uint256 a, uint256 c) internal pure override returns (uint256) {
        return 2 * b + 3 * a + 4 * c;
    }

    function parentFun() external pure override returns (uint256) {
        return 1;
    }

    function f(uint256 k) internal pure returns (uint256 d) {
        return k;
    }

    function f(uint256 a, uint256 b) internal pure returns (uint256 d) {
        return a + b;
    }

    function ifElse(bool flag) internal pure returns (uint256 d) {
        if (flag) return f(3);
        else return f(3, 7);
    }

    function named3(uint256 b, uint256 a, uint256 c) internal pure returns (uint256) {
        return 2 * b + 3 * a + 4 * c;
    }

    function mutableWithViewOverride() internal view override {}

    function mutableWithPureOverride() internal pure override {}

    function viewWithPureOverride() internal pure override {}

    /// solc: semanticTests/inheritance/access_base_storage.sol
    function accessBaseStorage() public {
        bool ok = setData(1, 2);
        uint256 viaBase = getViaBase();
        (uint256 base, uint256 derived) = getViaDerived();
        assert(ok);
        assert(viaBase == 1);
        assert(base == 1);
        assert(derived == 2);
    }

    /// solc: semanticTests/inheritance/derived_overload_base_function_direct.sol
    function derivedOverloadBaseDirect() public pure {
        uint256 r = ovDirect(1);
        assert(r == 2);
    }

    /// solc: semanticTests/inheritance/derived_overload_base_function_indirect.sol
    function derivedOverloadBaseIndirect() public pure {
        uint256 g = ovIndirect();
        uint256 h = ovIndirect(1);
        assert(g == 10);
        assert(h == 2);
    }

    /// solc: semanticTests/inheritance/overloaded_function_call_resolve_to_first.sol
    function overloadResolveToFirst() public pure {
        uint256 r = f(3);
        assert(r == 3);
    }

    /// solc: semanticTests/inheritance/overloaded_function_call_resolve_to_second.sol
    function overloadResolveToSecond() public pure {
        uint256 r = f(3, 7);
        assert(r == 10);
    }

    /// solc: semanticTests/inheritance/overloaded_function_call_with_if_else.sol
    function overloadWithIfElse() public pure {
        uint256 t = ifElse(true);
        uint256 e = ifElse(false);
        assert(t == 3);
        assert(e == 10);
    }

    /// solc: semanticTests/inheritance/inherited_function_named_parameters.sol
    function overrideNamedOrdered() public pure {
        uint256 r = named3({b: 1, a: 2, c: 3});
        assert(r == 20);
    }

    /// solc: semanticTests/virtualFunctions/virtual_function_calls.sol
    function virtualFunctionCallDirect() public pure {
        uint256 r = vg();
        assert(r == 2);
    }

    /// solc: semanticTests/virtualFunctions/virtual_override_changing_mutability_internal.sol
    function overrideChangingMutability() public {
        mutability();
    }


    /// solc: smtCheckerTests/inheritance/state_variables_2.sol
    /// @custom:key box
    function baseStateVariablesChain(uint y) public {
        require(y == 99);
        require(x < 10);
        z = x + y;
        uint r = z;
        assert(r < 150);
    }

    /// solc: smtCheckerTests/inheritance/state_variables_3.sol
    /// @custom:key box
    function baseStateVariablesPrivate(uint y) public {
        require(y == 99);
        require(x < 10);
        zp = x + y;
        uint r = zp;
        assert(r < 150);
    }

    /// solc: semanticTests/getters/value_types.sol
    function getterValueTypes() public {
        pa = 3;
        pb = 4;
        pc = 5;
        pd = 6;
        ph = true;
        uint a = pa;
        uint b = pb;
        uint c = pc;
        uint d = pd;
        bool h = ph;
        assert(a == 3);
        assert(b == 4);
        assert(c == 5);
        assert(d == 6);
        assert(h);
    }

    /// solc: semanticTests/getters/mapping.sol
    function getterNestedMapping() public {
        gx[1][2] = 3;
        uint r = gx[1][2];
        assert(r == 3);
    }

    /// solc: semanticTests/getters/mapping_with_names.sol
    function getterMappingWithNames() public {
        named[1][2] = 3;
        uint r = named[1][2];
        assert(r == 3);
    }

    /// solc: semanticTests/getters/mapping_to_struct.sol
    function getterMappingToStruct() public {
        gs[1][2].a = 3;
        gs[1][2].b = 4;
        gs[1][2].c = 5;
        gs[1][2].d = 6;
        uint a = gs[1][2].a;
        uint b = gs[1][2].b;
        uint c = gs[1][2].c;
        uint d = gs[1][2].d;
        assert(a == 3);
        assert(b == 4);
        assert(c == 5);
        assert(d == 6);
    }

    /// solc: semanticTests/getters/mapping_array_struct.sol
    /// @custom:key box
    function getterMappingArrayStruct() public {
        require(gm[1].length == 0);
        gm[1].push().a = 1;
        gm[1][0].b = 2;
        gm[1].push().a = 3;
        gm[1][1].b = 4;
        gn[1][0].a = 7;
        gn[1][0].b = 8;
        gn[1][1].a = 9;
        gn[1][1].b = 10;
        uint n = gm[1].length;
        uint ma0 = gm[1][0].a;
        uint mb0 = gm[1][0].b;
        uint ma1 = gm[1][1].a;
        uint mb1 = gm[1][1].b;
        uint na0 = gn[1][0].a;
        uint nb0 = gn[1][0].b;
        uint na1 = gn[1][1].a;
        uint nb1 = gn[1][1].b;
        assert(n == 2);
        assert(ma0 == 1);
        assert(mb0 == 2);
        assert(ma1 == 3);
        assert(mb1 == 4);
        assert(na0 == 7);
        assert(nb0 == 8);
        assert(na1 == 9);
        assert(nb1 == 10);
    }

    /// solc: semanticTests/getters/array_mapping_struct.sol
    /// @custom:key box
    function getterArrayMappingStruct() public {
        require(gam.length == 0);
        gam.push();
        gam.push();
        gam[1][0].a = 1;
        gam[1][0].b = 2;
        gam[1][1].a = 3;
        gam[1][1].b = 4;
        gan[1][0].a = 7;
        gan[1][0].b = 8;
        gan[1][1].a = 9;
        gan[1][1].b = 10;
        uint n = gam.length;
        uint ma0 = gam[1][0].a;
        uint mb0 = gam[1][0].b;
        uint ma1 = gam[1][1].a;
        uint mb1 = gam[1][1].b;
        uint na0 = gan[1][0].a;
        uint nb0 = gan[1][0].b;
        uint na1 = gan[1][1].a;
        uint nb1 = gan[1][1].b;
        assert(n == 2);
        assert(ma0 == 1);
        assert(mb0 == 2);
        assert(ma1 == 3);
        assert(mb1 == 4);
        assert(na0 == 7);
        assert(nb0 == 8);
        assert(na1 == 9);
        assert(nb1 == 10);
    }

    /// solc: semanticTests/getters/arrays.sol
    /// @custom:key box
    function getterArrays() public {
        require(ga[1].length == 0);
        ga[1].push(3);
        ga[1].push(4);
        uint n = ga[1].length;
        uint r0 = ga[1][0];
        uint r1 = ga[1][1];
        assert(n == 2);
        assert(r0 == 3);
        assert(r1 == 4);
    }

    /// solc: semanticTests/inheritance/inherited_constant_state_var.sol
    function inheritedConstantStateVar() public pure {
        uint256 r = K;
        assert(r == 7);
    }

    /// solc: semanticTests/virtualFunctions/internal_virtual_function_calls.sol
    function internalVirtualFunctionCalls() public pure {
        uint256 r = ivf();
        assert(r == 2);
    }

    /// solc: semanticTests/virtualFunctions/virtual_function_calls.sol
    function virtualFunctionCallViaBase() public pure {
        uint256 r = vf();
        assert(r == 2);
    }

    /// solc: semanticTests/inheritance/inherited_function_named_parameters.sol
    function inheritedNamedOverrideUnordered() public pure {
        uint256 r = nf({c: 3, b: 1, a: 2});
        assert(r == 20);
    }
}
