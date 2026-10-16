// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of smtCheckerTests/{control_flow,bmc_coverage,simple,complex,invariants,verification_target}.
contract SolcSmtControlFlow {
    struct S { uint x; }

    uint counter;
    uint c;
    uint ya;
    uint yb;
    uint yc;
    bool flag;
    S s;
    uint constant X = 32**22 + 8;
    uint[] arr;
    int ix;
    int iy;
    int iz;
    bool pa;
    bool pb;
    bool pc;
    bool pd;
    bool pe;
    bool pf;
    S destination;
    S indirect1;
    S indirect2;
    uint varTainted;
    uint varNotTainted;
    uint varDependant;
    uint varState;
    uint ux;

    modifier m(uint z) {
        uint y = 3;
        if (z == 10) counter = 2 + y;
        _;
        if (z == 10) counter = 4 + y;
    }

    modifier mGe(uint z) {
        uint y = 3;
        if (z >= 10) counter = 2 + y;
        _;
        if (z >= 10) counter = 4 + y;
    }

    modifier mTrue() {
        if (true) _;
    }

    function incCounter() internal returns (uint) {
        counter = counter + 1;
        return counter;
    }

    function incCounter2() internal returns (uint) {
        return incCounter();
    }

    function setFlag(bool v) internal returns (bool) {
        flag = v;
        return flag;
    }

    function gAddr() internal pure returns (address) {
        address a;
        a = address(0);
        return a;
    }

    function hAddr() internal pure returns (address) {
        address a;
        return a;
    }

    function add(uint x, uint y) internal pure returns (uint) {
        if (y == 0) return x;
        if (y == 1) return ++x;
        if (y == 2) return x + 2;
        return x + y;
    }

    function addWrites(uint x, uint y) internal returns (uint) {
        c = 0xff;
        if (y == 0) return x;
        c = 0xffff;
        if (y == 1) return ++x;
        c = 0xffffff;
        if (y == 2) return x + 2;
        c = 0xffffffff;
        return x + y;
    }

    function nestedIf(uint a, uint b) internal pure returns (uint) {
        if (a < 5) {
            if (b > 1) {
                return 0;
            }
        }
        if (a == 2 && b == 2) {
            return 42;
        } else {
            return 1;
        }
    }

    function branches(uint a) internal pure returns (uint) {
        if (a == 0) {
            return 0;
        } else {
            return 42;
        }
    }

    function simpleIf(uint a, uint b) internal pure returns (uint) {
        if (a == 0) {
            return 0;
        }
        return b / a;
    }

    function f1() internal m(10) { counter = 3; }
    function f2() internal m(10) m(12) { counter = 3; }
    function f3() internal m(8) { counter = 3; }
    function f4() internal mGe(10) mGe(12) { counter = 3; }

    function conditionalIncrement() internal {
        if (counter == 0) return;
        counter = 1;
    }

    function conditionalIncrementStruct() internal {
        if (s.x == 0) return;
        s.x = 1;
    }

    function conditionalIncrementStructLiteral() internal {
        if (s.x == 0) return;
        s.x = 1;
    }

    function conditionalStore() internal {
        if (arr[1] == 0) return;
        arr[1] = 1;
    }

    function conditionalIncrementTuple() internal {
        if (ya == 0) {
            (ya, yb) = (2, 2);
            return;
        }
        (ya, yb) = (1, 1);
    }

    function ctorB(int b) internal {
        if (b > 0) {
            ix = 1;
            return;
        } else {
            ix = 2;
            return;
        }
    }

    function diamondB(int a) internal {
        if (a >= 0) {
            iy = 1;
            return;
        }
        ix = 1;
        iy = 2;
    }

    function diamondC(int a) internal {
        if (a >= 0) {
            iz = 1;
            return;
        }
        ix = -1;
        iz = 2;
    }

    function initX() internal pure returns (uint) {
        return 42;
    }

    function resetAon() internal {
        pa = false;
        pb = false;
        pc = false;
        pd = false;
        pe = false;
        pf = false;
    }

    function pressA() public { if (pe) { pa = true; } else { resetAon(); } }
    function pressB() public { if (pc) { pb = true; } else { resetAon(); } }
    function pressC() public { if (pa) { pc = true; } else { resetAon(); } }
    function pressD() public { pd = true; }
    function pressE() public { if (pd) { pe = true; } else { resetAon(); } }
    function pressF() public { if (pb) { pf = true; } else { resetAon(); } }

    function f2Args(uint x, uint y) internal {
        varTainted = x;
        varNotTainted = y;
    }

    function bar() internal view returns (uint) {
        return (varState);
    }

    function simpleIf2(uint a) internal pure returns (uint) {
        if (a == 0) {
            return 0;
        }
        return 1;
    }

    function ctorA(int a) internal {
        ix = a;
    }

    function ctorBInit(int a) internal {
        ctorA(-a);
        if (a > 0) {
            iy = 2;
            return;
        } else {
            iy = 3;
        }
        iy = 4;
    }

    function ctorBAlt(int a) internal {
        if (a > 0) {
            ux = 2;
            return;
        }
        ux = 3;
    }

    /// solc: smtCheckerTests/control_flow/assignment_in_declaration.sol
    function assignmentInDeclaration() public pure {
        uint a = 2;
        assert(a == 2);
    }

    /// solc: smtCheckerTests/control_flow/branches_assert_condition_1.sol
    /// @custom:key box
    function branchesAssertCondition1(uint x) public pure {
        require(x >= 0);
        if (x > 10) {
            assert(x > 9);
        } else {
            assert(x < 11);
        }
    }

    /// solc: smtCheckerTests/control_flow/branches_assert_condition_2.sol
    /// @custom:key box
    function branchesAssertCondition2(uint x) public pure {
        require(x >= 0);
        if (x > 10) {
            assert(x > 9);
        } else if (x > 2) {
            assert(x <= 10 && x > 2);
        } else {
            assert(0 <= x && x <= 2);
        }
    }

    /// solc: smtCheckerTests/control_flow/branches_inside_modifiers_1.sol
    function branchesInsideModifiers1() public {
        counter = 0;
        f1();
        assert(counter == 7);
    }

    /// solc: smtCheckerTests/control_flow/branches_inside_modifiers_2.sol
    function branchesInsideModifiers2() public {
        counter = 0;
        f2();
        assert(counter == 7);
    }

    /// solc: smtCheckerTests/control_flow/branches_inside_modifiers_3.sol
    function branchesInsideModifiers3() public {
        counter = 0;
        f3();
        assert(counter == 3);
    }

    /// solc: smtCheckerTests/control_flow/branches_inside_modifiers_4.sol
    function branchesInsideModifiers4() public {
        counter = 0;
        f4();
        assert(counter == 7);
    }

    /// solc: smtCheckerTests/control_flow/branches_merge_variables_1.sol
    /// @custom:key box
    function branchesMergeVariables1(uint x) public pure {
        require(x >= 0);
        uint a = 3;
        if (x > 10) {
        }
        assert(a == 3);
    }

    /// solc: smtCheckerTests/control_flow/branches_merge_variables_2.sol
    /// @custom:key box
    function branchesMergeVariables2(uint x) public pure {
        require(x >= 0);
        uint a = 3;
        if (x > 10) {
            a = 3;
        }
        assert(a == 3);
    }

    /// solc: smtCheckerTests/control_flow/branches_merge_variables_3.sol
    /// @custom:key box
    function branchesMergeVariables3(uint x) public pure {
        require(x >= 0);
        uint a = 3;
        if (x > 10) {
        } else {
            a = 3;
        }
        assert(a == 3);
    }

    /// solc: smtCheckerTests/control_flow/branches_merge_variables_4.sol
    /// @custom:key box
    function branchesMergeVariables4(uint x) public pure {
        require(x >= 0);
        uint a = 3;
        if (x > 10) {
            assert(a == 3);
        } else {
            assert(a == 3);
        }
        assert(a == 3);
    }

    /// solc: smtCheckerTests/control_flow/branches_merge_variables_5.sol
    /// @custom:key box
    function branchesMergeVariables5(uint x) public pure {
        require(x >= 0);
        uint a = 2;
        if (x > 10) {
            a = 3;
        } else {
            a = 3;
        }
        assert(a == 3);
    }

    /// solc: smtCheckerTests/control_flow/branches_merge_variables_6.sol
    /// @custom:key box
    function branchesMergeVariables6(uint x) public pure {
        require(x >= 0);
        uint a = 2;
        if (x > 10) {
            a = 3;
        } else {
            a = 4;
        }
        assert(a >= 3);
    }

    /// solc: smtCheckerTests/control_flow/function_call_inside_branch.sol
    function functionCallInsideBranch() public pure {
        if (true) {
            address a = gAddr();
            assert(a == address(0));
        }
    }

    /// solc: smtCheckerTests/control_flow/function_call_inside_branch_2.sol
    function functionCallInsideBranch2() public pure {
        if (true) {
            address a = gAddr();
            assert(a == address(0));
        } else {
            address b = gAddr();
            assert(b == address(0));
        }
    }

    /// solc: smtCheckerTests/control_flow/function_call_inside_else_branch.sol
    function functionCallInsideElseBranch() public pure {
        if (true) {
        } else {
            address a = gAddr();
            assert(a == address(0));
        }
    }

    /// solc: smtCheckerTests/control_flow/function_call_inside_placeholder_inside_modifier_branch.sol
    /// @custom:key box
    function functionCallInsidePlaceholderInsideModifierBranch(address a) public pure mTrue {
        require(a == address(1));
        if (true) {
            a = gAddr();
            assert(a == address(0));
        }
    }

    /// solc: smtCheckerTests/control_flow/require.sol
    /// @custom:key box
    function requireFalseUnreachable() public pure {
        require(false);
        assert(false);
    }

    /// solc: smtCheckerTests/control_flow/require.sol
    /// @custom:key box
    function requireFalseInBranch(uint bb) public pure {
        require(bb >= 0 && bb <= 1);
        bool b = bb == 1;
        if (b) require(false);
        assert(!b);
    }

    /// solc: smtCheckerTests/control_flow/return_1.sol
    function return1() public pure {
        uint r0 = add(100, 0);
        assert(r0 == 100);
        uint r1 = add(100, 1);
        assert(r1 == 101);
        uint r2 = add(100, 2);
        assert(r2 == 102);
        uint r3 = add(100, 100);
        assert(r3 == 200);
    }

    /// solc: smtCheckerTests/control_flow/return_2.sol
    function return2() public {
        uint r0 = addWrites(100, 0);
        assert(r0 == 100);
        assert(c == 0xff);
        uint r1 = addWrites(100, 1);
        assert(r1 == 101);
        assert(c == 0xffff);
        uint r2 = addWrites(100, 2);
        assert(r2 == 102);
        assert(c == 0xffffff);
        uint r3 = addWrites(100, 100);
        assert(r3 == 200);
        assert(c == 0xffffffff);
    }

    /// solc: smtCheckerTests/control_flow/revert.sol
    /// @custom:key box
    function revertUnreachable() public pure {
        revert();
        assert(false);
    }

    /// solc: smtCheckerTests/control_flow/revert.sol
    /// @custom:key box
    function revertInBranch(uint bb) public pure {
        require(bb >= 0 && bb <= 1);
        bool b = bb == 1;
        if (b) revert();
        assert(!b);
    }

    /// solc: smtCheckerTests/control_flow/revert_complex_flow.sol
    /// @custom:key box
    function revertComplexFlow(uint bb, uint a) public pure {
        require(bb >= 0 && bb <= 1 && a >= 0 && a <= 256);
        bool b = bb == 1;
        if (b) revert();
        uint c2 = a + 1;
        if (b) c2--;
        else c2++;
        assert(c2 != a);
    }

    /// solc: smtCheckerTests/control_flow/short_circuit_and.sol
    function shortCircuitAnd() public {
        counter = 0;
        bool b = (incCounter() == 0) && (incCounter() == 0);
        assert(counter == 1);
        assert(!b);
    }

    /// solc: smtCheckerTests/control_flow/short_circuit_and_need_both.sol
    function shortCircuitAndNeedBoth() public {
        counter = 0;
        bool b = (incCounter() > 0) && (incCounter() > 0);
        assert(counter == 2);
        assert(b);
    }

    /// solc: smtCheckerTests/control_flow/short_circuit_or.sol
    function shortCircuitOr() public {
        counter = 0;
        bool b = (incCounter() > 0) || (incCounter() > 0);
        assert(counter == 1);
        assert(b);
    }

    /// solc: smtCheckerTests/control_flow/short_circuit_or_need_both.sol
    function shortCircuitOrNeedBoth() public {
        counter = 0;
        bool b = (incCounter() > 1) || (incCounter() > 1);
        assert(counter == 2);
        assert(b);
    }

    /// solc: smtCheckerTests/control_flow/short_circuit_or_inside_branch.sol
    /// @custom:key box
    function shortCircuitOrInsideBranch(uint aa) public {
        require(aa >= 0 && aa <= 1);
        bool a = aa == 1;
        bool b;
        if (a) {
            counter = 0;
            b = (incCounter() > 0) || (incCounter() > 0);
            assert(counter == 1);
            assert(b);
        } else {
            counter = 100;
            b = (incCounter() == 0) || (incCounter() > 0);
            assert(counter == 102);
        }
    }

    /// solc: smtCheckerTests/control_flow/short_circuit_and_inside_branch.sol
    function shortCircuitAndInsideBranch() public {
        bool b;
        counter = 100;
        b = incCounter() > 0;
        assert(b);
    }

    /// solc: smtCheckerTests/control_flow/short_circuit_and_touched_function.sol
    function shortCircuitAndTouchedFunction() public {
        bool c1 = setFlag(false) && (flag == true);
        assert(!c1);
        bool c2 = (flag == false) && setFlag(true);
        assert(c2);
        bool c3 = setFlag(false) && setFlag(true);
        assert(!c3);
        bool c4 = setFlag(false) && (flag == true);
        assert(!c4);
        bool c5 = setFlag(true) && flag;
        assert(c5);
    }

    /// solc: smtCheckerTests/control_flow/short_circuit_or_touched_function.sol
    function shortCircuitOrTouchedFunction() public {
        bool c1 = setFlag(true) || (flag == false);
        assert(c1);
        bool c2 = (flag == true) || setFlag(false);
        assert(c2);
        bool c3 = setFlag(true) || setFlag(false);
        assert(c3);
        bool c4 = setFlag(true) || (flag == false);
        assert(c4);
        bool c5 = setFlag(false) || flag;
        assert(!c5);
    }

    /// solc: smtCheckerTests/control_flow/side_effects_inside_if_1.sol
    function sideEffectsInsideIf1() public pure {
        uint x;
        if (++x < 3) {}
        assert(x == 1);
    }

    /// solc: smtCheckerTests/control_flow/side_effects_inside_if_2.sol
    /// @custom:key box
    function sideEffectsInsideIf2() public {
        require(counter < 1000);
        uint y = counter;
        if (incCounter() < 3) {}
        uint e = y + 1;
        assert(counter == e);
    }

    /// solc: smtCheckerTests/control_flow/side_effects_inside_if_3.sol
    /// @custom:key box
    function sideEffectsInsideIf3() public {
        require(counter < 1000);
        uint y = counter;
        if (incCounter2() < 3) {}
        uint e = y + 1;
        assert(counter == e);
    }

    /// solc: smtCheckerTests/control_flow/side_effects_inside_if_4.sol
    function sideEffectsInsideIf4() public pure {
        uint x = 2;
        if (--x < 3) {}
        assert(x == 1);
    }

    /// solc: smtCheckerTests/control_flow/side_effects_inside_ternary_1.sol
    function sideEffectsInsideTernary1() public pure {
        uint x;
        uint y = (++x < 3) ? ++x : --x;
        assert(y == x);
        assert(x == 2);
    }

    /// solc: smtCheckerTests/control_flow/side_effects_inside_ternary_2.sol
    /// @custom:key box
    function sideEffectsInsideTernary2() public {
        require(counter < 1000);
        uint z = counter;
        uint y = (incCounter() < 3) ? incCounter() : incCounter();
        assert(y == counter);
        uint e = z + 2;
        assert(counter == e);
    }

    /// solc: smtCheckerTests/control_flow/side_effects_inside_ternary_3.sol
    /// @custom:key box
    function sideEffectsInsideTernary3() public {
        require(counter < 1000);
        uint z = counter;
        uint y = (incCounter2() < 3) ? incCounter2() : incCounter2();
        assert(y == counter);
        uint e = z + 2;
        assert(counter == e);
    }

    /// solc: smtCheckerTests/control_flow/side_effects_inside_ternary_4.sol
    function sideEffectsInsideTernary4() public pure {
        uint x = 2;
        uint y = (--x < 3) ? --x : 0;
        assert(y == x);
        assert(x == 0);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/nested_if.sol
    /// @custom:key box
    function nestedIfNever42(uint a, uint b) public pure {
        require(a >= 0 && b >= 0);
        uint r = nestedIf(a, b);
        assert(r != 42);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/return_in_both_branches.sol
    function returnInBothBranches() public pure {
        uint r0 = branches(0);
        assert(r0 == 0);
        uint r1 = branches(1);
        assert(r1 == 42);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/simple_if.sol
    /// @custom:key box
    function simpleIfGuardsDivision(uint a, uint b) public pure {
        require(a >= 0 && b >= 0);
        simpleIf(a, b);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/simple_if_state_var.sol
    /// @custom:key box
    function simpleIfStateVar() public {
        require(counter == 0);
        conditionalIncrement();
        assert(counter == 0);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/simple_if_struct.sol
    /// @custom:key box
    function simpleIfStruct() public {
        require(s.x == 0);
        conditionalIncrementStruct();
        assert(s.x == 0);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/simple_if_struct_2.sol
    /// @custom:key box
    function simpleIfStruct2() public {
        require(s.x == 0);
        conditionalIncrementStructLiteral();
        assert(s.x == 0);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/simple_if_array.sol
    /// @custom:key box
    function simpleIfArray() public {
        require(arr.length >= 2);
        require(arr[1] == 0);
        conditionalStore();
        assert(arr[1] == 0);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/simple_if_tuple.sol
    /// @custom:key box
    function simpleIfTuple() public {
        require(ya == 0);
        require(yb == 0);
        conditionalIncrementTuple();
        assert(ya == 2);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/triple_nested_if.sol
    function tripleNestedIf() public view {
        if (ya == 0) {
            if (yb == 0) {
                if (yc == 0) {
                    return;
                }
            }
        }
        uint a = ya;
        uint b = yb;
        uint d = yc;
        assert(a != 0 || b != 0 || d != 0);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/constructors.sol
    /// @custom:key box
    function constructorsReturnInBothBranches(int a) public {
        require(a >= -57896044618658097711785492504343953926634992332820282019728792003956564819967 && a <= 57896044618658097711785492504343953926634992332820282019728792003956564819967);
        ix = 0;
        ctorB(a);
        assert(a > 0 || ix == 2);
        assert(a <= 0 || ix == 1);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/constructor_state_variable_init_diamond.sol
    function constructorDiamondD1() public {
        ix = 0;
        iy = 0;
        iz = 0;
        diamondB(1);
        diamondC(1);
        assert(ix == 0);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/constructor_state_variable_init_diamond.sol
    function constructorDiamondD2() public {
        ix = 0;
        iy = 0;
        iz = 0;
        diamondB(1);
        diamondC(-1);
        int e = -1;
        assert(ix == e);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/constructor_state_variable_init_diamond.sol
    function constructorDiamondD3() public {
        ix = 0;
        iy = 0;
        iz = 0;
        diamondB(-1);
        diamondC(1);
        assert(ix == 1);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/constructor_state_variable_init_diamond.sol
    function constructorDiamondD4() public {
        ix = 0;
        iy = 0;
        iz = 0;
        diamondB(-1);
        diamondC(-1);
        int e = -1;
        assert(ix == e);
    }

    /// solc: smtCheckerTests/verification_target/simple_assert_with_require.sol
    /// @custom:key box
    function simpleAssertWithRequire(uint a) public pure {
        require(a < 10);
        assert(a < 20);
    }

    /// solc: smtCheckerTests/verification_target/constant_condition_2.sol
    function constantCondition2NeverReverts(uint x) public pure {
        if (x >= 10) { if (x < 10) { revert(); } }
    }

    /// solc: smtCheckerTests/bmc_coverage/assert.sol
    function bmcConditionUnreachable(uint x) public pure {
        if (false) {
            if (x != 2) {
            }
        }
    }

    /// solc: smtCheckerTests/bmc_coverage/assert_in_constructor.sol
    function assertInConstructor() public {
        ya = initX();
        assert(ya == 42);
        yb = ya;
    }

    /// solc: smtCheckerTests/invariants/loop_basic_for.sol
    /// @custom:key box
    function loopBasicFor(uint x) public pure {
        require(x >= 0);
        uint y;
        /// @custom:key invariant 0 <= y && y <= x
        for (y = 0; y < x; ++y) {}
        assert(y == x);
    }

    /// solc: smtCheckerTests/invariants/loop_basic.sol
    /// @custom:key box
    function loopBasic(uint x) public pure {
        require(x > 0);
        uint y;
        /// @custom:key invariant 0 <= y && y <= x
        while (y < x) ++y;
        assert(y == x);
    }

    /// solc: smtCheckerTests/invariants/loop_nested.sol
    function loopNested() public pure {
        uint x = 10;
        uint y;
        while (y < x) {
            ++y;
            x = 0;
            while (x < 10) ++x;
            assert(x == 10);
        }
    }

    /// solc: smtCheckerTests/invariants/loop_nested_for.sol
    function loopNestedFor() public pure {
        uint x;
        uint y;
        for (x = 10; y < x; ++y) {
            for (x = 0; x < 10; ++x) {}
            assert(x == 10);
        }
    }

    /// solc: smtCheckerTests/invariants/array_access.sol
    /// @custom:key box
    function arrayAccess() public {
        require(arr.length == 2);
        arr[0] = 1;
        arr[1] = 2;
        uint a0 = arr[0];
        uint a1 = arr[1];
        assert(a1 > a0);
    }

    /// solc: smtCheckerTests/invariants/struct_access.sol
    function structAccess() public {
        s.x = 1;
        assert(s.x > 0);
    }

    /// solc: smtCheckerTests/invariants/unary_minus_formatting.sol
    function unaryMinusFormatting() public {
        ix = -1;
        assert(ix == -1);
    }

    /// solc: smtCheckerTests/invariants/state_machine_1.sol
    /// @custom:key box
    function stateMachineStep(uint t) public {
        require(counter < 3 && t >= 0 && t < 4);
        if (t == 0) { if (counter == 0) counter = 1; }
        else if (t == 1) { if (counter == 1) counter = 2; }
        else if (t == 2) { if (counter == 2) counter = 0; }
        else { if (counter == 7) counter = 100; }
        assert(counter < 3);
        assert(counter < 9);
    }

    /// solc: smtCheckerTests/invariants/aon_blog_post.sol
    function aonBlogPostSolvable() public {
        resetAon();
        pressD();
        pressE();
        pressA();
        pressC();
        pressB();
        pressF();
        assert(pf);
    }

    /// solc: smtCheckerTests/complex/slither/data_dependency.sol
    /// @custom:key box
    function dataDependencyReferenceSet3(uint sourceTaint) public {
        require(sourceTaint >= 0);
        indirect1.x = 7;
        S storage ref = indirect1;
        if (true) {
            ref = indirect2;
        }
        ref.x = sourceTaint;
        assert(indirect2.x == sourceTaint);
        assert(indirect1.x == 7);
    }

    /// solc: smtCheckerTests/complex/slither/data_dependency.sol
    /// @custom:key box
    function dataDependencyPropagateThroughArguments(uint userInput) public {
        require(userInput >= 0);
        f2Args(userInput, 4);
        varDependant = varTainted;
        assert(varDependant == userInput);
        assert(varNotTainted == 4);
    }

    /// solc: smtCheckerTests/complex/slither/data_dependency.sol
    function dataDependencyPropagateThroughReturnValue() public {
        varState = 9;
        varDependant = bar();
        assert(varDependant == 9);
    }

    /// solc: smtCheckerTests/control_flow/function_call_inside_branch_3.sol
    function functionCallInsideBranch3() public pure {
        if (true) {
            address a = gAddr();
            assert(a == address(0));
        }
        if (true) {
            address a = gAddr();
            assert(a == address(0));
        }
    }

    /// solc: smtCheckerTests/control_flow/function_call_inside_branch_4.sol
    function functionCallInsideBranch4() public pure {
        if (true) {
            address a = gAddr();
            assert(a == address(0));
        }
        if (true) {
            address a = hAddr();
            assert(a == address(0));
        }
    }

    /// solc: smtCheckerTests/control_flow/ways_to_merge_variables_1.sol
    /// @custom:key box
    function waysToMergeVariables1(uint x) public pure {
        require(x == 11);
        uint a = 3;
        if (x > 10) {
            a++;
        }
        assert(a == 4);
    }

    /// solc: smtCheckerTests/control_flow/ways_to_merge_variables_2.sol
    /// @custom:key box
    function waysToMergeVariables2(uint x) public pure {
        require(x == 11);
        uint a = 3;
        if (x > 10) {
            ++a;
        }
        assert(a == 4);
    }

    /// solc: smtCheckerTests/control_flow/ways_to_merge_variables_3.sol
    /// @custom:key box
    function waysToMergeVariables3(uint x) public pure {
        require(x == 11);
        uint a = 3;
        if (x > 10) {
            a = 5;
        }
        assert(a == 5);
    }

    /// solc: smtCheckerTests/bmc_coverage/assert.sol
    /// @custom:key box
    function bmcContradictoryRequires(uint x) public pure {
        require(x == 2);
        require(x != 2);
        assert(false);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/simple_if2.sol
    /// @custom:key box
    function simpleIf2Counterexample(uint a) public pure {
        require(a == 0);
        uint r = simpleIf2(a);
        assert(r == 0);
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/constructor_state_variable_init.sol
    /// @custom:key box
    function constructorStateVariableInit(int a) public {
        require(a >= -57896044618658097711785492504343953926634992332820282019728792003956564819967 && a <= 57896044618658097711785492504343953926634992332820282019728792003956564819967);
        ctorBInit(a);
        assert(iy != 3);
        if (a > 0) {
            assert(ix < 0 && iy == 2);
        } else {
            assert(ix >= 0 && iy == 4);
        }
    }

    /// solc: smtCheckerTests/control_flow/branches_with_return/constructor_state_variable_init_chain_alternate.sol
    /// @custom:key box
    function constructorStateVariableInitChainAlternate(int a) public {
        require(a >= -57896044618658097711785492504343953926634992332820282019728792003956564819967 && a <= 57896044618658097711785492504343953926634992332820282019728792003956564819967);
        ux = 1;
        ctorBAlt(a);
        assert(a > 0 || ux == 3);
        assert(a <= 0 || ux == 2);
    }

    /// solc: smtCheckerTests/complex/slither/const_state_variables.sol
    function constStateVariable() public pure {
        uint r = X;
        uint e = 32**22 + 8;
        assert(r == e);
    }
}
