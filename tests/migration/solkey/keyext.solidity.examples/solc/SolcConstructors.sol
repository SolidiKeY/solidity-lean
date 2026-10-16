// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SolcConstructors {
    enum E { READ, WRITE }
    enum Choice { GoLeft, GoRight, GoStraight, Sit }

    struct S {
        uint x;
        uint[] a;
    }

    uint constant X = 56;
    uint public test;
    uint i;
    uint k;
    uint m_a;
    uint m_base;
    uint m_derived;
    uint name;
    bool flag;
    uint ia;
    uint ib;
    uint ic;
    uint id;
    uint ix;
    uint iy;
    int sx;
    int sy;
    uint[] xs;
    uint[] ms;
    uint mx;
    uint x;
    uint y;
    uint z;

    modifier n() {
        _;
        x = 7;
    }

    function setName(uint _name) private {
        name = _name;
    }

    function readA() internal view returns (uint) {
        return ia;
    }

    function pushX(uint v) internal returns (uint) {
        xs.push(v);
    }

    function fx(uint v) internal view returns (uint) {
        assert(v > 0);
        assert(x == 0);
        return v;
    }

    function getX() internal view returns (uint) {
        return x;
    }

    function incX() internal returns (uint) {
        x = x + 1;
        return x;
    }

    function initHierarchy(int a) internal {
        sx = -a;
        if (a > 0) {
            sy = 2;
        } else {
            sy = 4;
        }
    }

    function initWithModifier(uint v) internal n {
        x = v;
    }

    function helper(uint v, bool f) internal {
        name = v;
        flag = f;
    }

    function part(uint j) internal view returns (uint) {
        return ms[j];
    }

    function identity(uint[] memory s) internal pure returns (uint[] memory) {
        return s;
    }

    function add(uint a, uint b) internal pure returns (uint) {
        return a + b;
    }

    function fe(uint v) internal pure returns (uint) {
        return add(v, 2);
    }

    function allocate(bool b) internal pure returns (E) {
        if (b) return E.READ;
        return E.WRITE;
    }

    function allocateS(uint _x, uint _f) internal pure returns (S memory) {
        S memory s;
        s.x = _x;
        s.a = new uint[](1);
        s.a[0] = _f;
        return s;
    }

    /// solc: semanticTests/constructor/state_variable_initialization.sol
    function stateVariableInitialization() public {
        i = 1;
        k = 2;
        i = i + i;
        k = k - i;
        assert(i == 2);
        assert(k == 0);
    }

    /// solc: semanticTests/constructor/base_constructor_arguments.sol
    function baseConstructorArguments() public {
        m_a = 7;
        uint t = m_a;
        m_a *= t;
        uint r = m_a;
        assert(r == 49);
    }

    /// solc: semanticTests/constructor/inline_member_init_inheritence_without_constructor.sol
    function inlineMemberInit() public {
        m_base = 5;
        m_derived = 6;
        uint b = m_base;
        uint d = m_derived;
        assert(b == 5);
        assert(d == 6);
    }

    /// solc: semanticTests/constructor/functions_called_by_constructor.sol
    function functionsCalledByConstructor() public {
        setName(0x616263);
        uint r = name;
        assert(r == 0x616263);
    }

    /// solc: semanticTests/constructor/constructor_arguments_internal.sol
    function constructorArgumentsInternal() public {
        helper(0x616263, true);
        bool f = flag;
        uint r = name;
        assert(f == true);
        assert(r == 0x616263);
    }

    /// solc: semanticTests/constructor/order_of_evaluation.sol
    /// @custom:key box
    function orderOfEvaluation() public {
        require(xs.length == 0);
        uint r1 = pushX(1);
        pushX(3);
        pushX(2);
        pushX(4);
        assert(r1 == 0);
        assert(xs.length == 4);
        assert(xs[0] == 1);
        assert(xs[1] == 3);
        assert(xs[2] == 2);
        assert(xs[3] == 4);
    }

    /// solc: semanticTests/constructor/arrays_in_constructors.sol
    function arraysInConstructors() public {
        uint[] memory s = new uint[](10);
        for (uint j = 0; j < 10; j++) s[j] = j + 1;
        mx = 7;
        ms = identity(s);
        uint r = mx;
        uint ch = part(7);
        assert(r == 7);
        assert(ch == 8);
    }

    /// solc: semanticTests/immutable/assign_from_immutables.sol
    function assignFromImmutables() public {
        ia = 1;
        ib = ia;
        ic = ib;
        id = ic;
        uint a = ia;
        uint b = ib;
        uint c = ic;
        uint d = id;
        assert(a == 1);
        assert(b == 1);
        assert(c == 1);
        assert(d == 1);
    }

    /// solc: semanticTests/immutable/delete.sol
    function deleteImmutable() public {
        ib = 0x42;
        delete ia;
        delete ib;
        ic = ib * 2 + ia;
        uint a = ia;
        uint b = ib;
        uint c = ic;
        assert(a == 0);
        assert(b == 0);
        assert(c == 0);
    }

    /// solc: semanticTests/immutable/fun_read_in_ctor.sol
    function funReadInCtor() public {
        ia = 3;
        ix = readA();
        uint rx = ix;
        uint ra = readA();
        assert(rx == 3);
        assert(ra == 3);
    }

    /// solc: semanticTests/immutable/read_in_ctor.sol
    function readInCtor() public {
        ia = 3;
        ix = ia;
        uint r = ix;
        assert(r == 3);
    }

    /// solc: semanticTests/immutable/multiple_initializations.sol
    /// @custom:key box
    function multipleInitializations() public {
        require(ix == 0);
        ix = ix + 1;
        ix += 2;
        iy = ix;
        ix += 8;
        ix += 4;
        ix += 16;
        ix += 32;
        ix += 64;
        ix += 128;
        uint r = ix;
        uint s = iy;
        assert(r == 0xff);
        assert(s == 3);
    }

    /// solc: semanticTests/immutable/increment_decrement.sol
    function incrementDecrement() public {
        sx = 1;
        sy = 3;
        sx--;
        --sx;
        sy++;
        ++sy;
        --sy;
        int a = sx;
        int b = sy;
        int expected = -1;
        assert(a == expected);
        assert(b == 4);
    }

    /// solc: semanticTests/immutable/stub.sol
    function immutableStub() public {
        ix = 42;
        iy = 23;
        uint a = ix;
        uint b = iy;
        uint twice = a + a;
        assert(twice == 84);
        assert(b == 23);
    }

    /// solc: semanticTests/scoping/c99_scoping_activation.sol (f)
    function c99ScopingAssignOuter() public pure {
        uint v = 7;
        {
            v = 3;
            uint v;
            v = 4;
        }
        assert(v == 3);
    }

    /// solc: semanticTests/scoping/c99_scoping_activation.sol (h)
    function c99ScopingReadOuter() public pure {
        uint v = 7;
        uint a;
        uint b;
        {
            v = 3;
            a = v;
            uint v = 4;
            b = v;
        }
        assert(v == 3);
        assert(a == 3);
        assert(b == 4);
    }

    /// solc: semanticTests/scoping/c99_scoping_activation.sol (i)
    function c99ScopingSelfInit() public pure {
        uint v = 7;
        uint a;
        {
            v = 3;
            uint v = v;
            a = v;
        }
        assert(v == 3);
        assert(a == 3);
    }

    /// solc: semanticTests/scoping/c99_scoping_activation.sol (g)
    function c99ScopingShadowDefault() public pure {
        uint v = 7;
        uint r;
        {
            v = 3;
            uint v;
            r = v;
        }
        assert(r == 0);
    }

    /// solc: semanticTests/immutable/uninitialized.sol (local form)
    function localDefaults() public pure {
        uint ru;
        bool rb;
        address ra;
        assert(ru == 0);
        assert(rb == false);
        assert(ra == address(0));
    }

    /// solc: semanticTests/constants/constant_variables.sol (enum default)
    function enumDefault() public pure {
        Choice c;
        assert(c == Choice.GoLeft);
    }

    /// solc: smtCheckerTests/functions/constructor_simple.sol
    /// @custom:key box
    function constructorSimple() public {
        require(x == 0);
        uint before = x;
        assert(before == 0);
        x = 10;
    }

    /// solc: smtCheckerTests/functions/constructor_state_value.sol
    function constructorStateValue() public {
        x = 5;
        uint before = x;
        assert(before == 5);
        x = 10;
    }

    /// solc: smtCheckerTests/functions/constructor_state_value_parameter.sol
    /// @custom:key box
    function constructorStateValueParameter(uint a, uint b) public {
        require(a == 3 && b == 4);
        x = 5;
        uint before = x;
        assert(before == 5);
        x = a + b;
    }

    /// solc: smtCheckerTests/array_members/pop_constructor_safe.sol
    function popConstructorSafe() public {
        uint l = xs.length;
        xs.push();
        xs.pop();
        uint after_ = xs.length;
        assert(after_ == l);
    }

    /// solc: smtCheckerTests/inheritance/constructor_state_variable_init.sol
    function constructorStateVariableInit() public {
        x = 2;
        uint v = x;
        assert(v == 2);
    }

    /// solc: smtCheckerTests/inheritance/constructor_state_variable_init_chain.sol
    function constructorStateVariableInitChain() public {
        x = 1;
        x = 2;
        x = 3;
        uint v = x;
        assert(v == 3);
        assert(v != 2);
    }

    /// solc: smtCheckerTests/inheritance/constructor_state_variable_init_asserts.sol
    function constructorStateVariableInitAsserts() public {
        initHierarchy(1);
        int a = sx;
        int b = sy;
        assert(b != 3);
        assert(a < 0 && b == 2);
        initHierarchy(0);
        a = sx;
        b = sy;
        assert(b != 3);
        assert(a >= 0 && b == 4);
    }

    /// solc: smtCheckerTests/inheritance/constructor_hierarchy_base_calls_with_side_effects_1.sol
    /// @custom:key box
    function constructorBaseCallsWithSideEffects() public {
        require(x == 0 && k == 0);
        uint b = x;
        uint zz = x;
        uint a = b + incX();
        x = a;
        k = zz;
        uint rx = x;
        uint rk = k;
        assert(rx == 1);
        assert(rk == 0);
        assert(rx != rk);
    }

    /// solc: smtCheckerTests/inheritance/constructor_state_variable_init_function_call.sol
    /// @custom:key box
    function constructorInitFunctionCall() public {
        require(x == 0);
        x = fx(2);
        uint v = x;
        assert(v == 2);
    }

    /// solc: smtCheckerTests/inheritance/constructor_uses_function_base.sol
    function constructorUsesFunctionBase() public {
        x = 42;
        y = getX();
        uint v = y;
        assert(v == 42);
    }

    /// solc: smtCheckerTests/functions/constructor_hierarchy_same_var.sol
    function constructorHierarchySameVar() public {
        x = 2;
        uint v = x;
        assert(v != 0);
    }

    /// solc: smtCheckerTests/functions/constructor_hierarchy_mixed_chain_local_vars.sol
    function constructorMixedChainLocalVars() public {
        uint f = 2;
        x = f;
        uint d = 3;
        x = d;
        uint b = 4;
        x = b;
        uint a1 = 4;
        uint v = x;
        assert(v == a1);
    }

    /// solc: smtCheckerTests/functions/constructor_hierarchy_modifier.sol
    function constructorHierarchyModifier() public {
        initWithModifier(2);
        uint v = x;
        assert(v != 4);
    }

    /// solc: smtCheckerTests/file_level/easy.sol
    function fileLevelEasy() public pure {
        uint r7 = fe(7);
        uint r8 = fe(8);
        assert(r7 == 9);
        assert(r8 != 9);
    }

    /// solc: smtCheckerTests/file_level/enum.sol
    function fileLevelEnum() public pure {
        E e1 = allocate(true);
        assert(e1 == E.READ);
        E e2 = allocate(false);
        assert(e2 != E.READ);
        E e3 = allocate(false);
        assert(e3 == E.WRITE);
    }

    /// solc: smtCheckerTests/file_level/struct.sol
    function fileLevelStruct() public pure {
        S memory s = allocateS(2, 1);
        uint x = s.x;
        uint a0 = s.a[0];
        assert(x == 2);
        assert(a0 == 1);
    }

    /// solc: semanticTests/variables/public_state_overridding.sol
    function publicStateOverridding() public {
        test = 2;
        uint r = test;
        assert(r == 2);
    }

    /// solc: semanticTests/constants/simple_constant_variables_test.sol
    function simpleConstantVariables() public pure {
        uint r = X;
        assert(r == 56);
    }
}
