// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of the internal-call tests of the solc compiler test suite:
/// `semanticTests/functionCall/`, `semanticTests/freeFunctions/` and
/// `smtCheckerTests/functions/`.
contract SolcFunctionCalls {
    uint x;
    uint a;
    uint y;
    uint[] data;

    struct S {
        uint x;
        uint y;
    }

    function internalFunction(uint p, uint q, uint s) internal pure returns (uint r) {
        r = p * 100 + q * 10 + s * 1;
    }

    function publicFunction(uint p, uint q, uint s) internal pure returns (uint r) {
        r = p * 100 + q * 10 + s * 1;
    }

    /// solc: semanticTests/functionCall/named_args.sol
    function namedArgsOrdered() public pure {
        uint internalOrdered = internalFunction({p: 1, q: 2, s: 3});
        uint publicOrdered = publicFunction({p: 1, q: 2, s: 3});
        assert(internalOrdered == 123);
        assert(publicOrdered == 123);
    }

    function ov() internal pure returns (uint) {
        return 0;
    }

    function ov(uint p) internal pure returns (uint) {
        return p;
    }

    function ov(uint p, uint q) internal pure returns (uint) {
        return p + q;
    }

    function ov(uint p, uint q, uint s) internal pure returns (uint) {
        return p + q + s;
    }

    function ovCall(uint num) internal pure returns (uint) {
        if (num == 0)
            return ov();
        if (num == 1)
            return ov({p: 1});
        if (num == 2)
            return ov({q: 1, p: 2});
        if (num == 3)
            return ov({s: 1, p: 2, q: 3});
        if (num == 4)
            return ov({q: 5, s: 1, p: 2});
        return 500;
    }

    /// solc: semanticTests/functionCall/named_args_overload.sol
    function namedArgsOverload() public pure {
        uint r0 = ovCall(0);
        uint r1 = ovCall(1);
        uint r2 = ovCall(2);
        uint r3 = ovCall(3);
        uint r4 = ovCall(4);
        uint r5 = ovCall(5);
        assert(r0 == 0);
        assert(r1 == 1);
        assert(r2 == 3);
        assert(r3 == 6);
        assert(r4 == 8);
        assert(r5 == 500);
    }

    function run(bool x1, uint x2) internal pure returns (uint y1, bool y2, uint y3) {
        y1 = x2;
        y2 = x1;
    }

    /// solc: semanticTests/functionCall/multiple_return_values.sol
    function multipleReturnValues() public pure {
        (uint y1, bool y2, uint y3) = run(true, 0xcd);
        assert(y1 == 0xcd);
        assert(y2);
        assert(y3 == 0);
    }

    function retA() internal pure returns (uint n) {
        return 0;
    }

    function retB() internal pure returns (uint n) {
        return 1;
    }

    function retC() internal pure returns (uint n) {
        return 2;
    }

    function retF() internal pure returns (uint n) {
        return 3;
    }

    /// solc: semanticTests/functionCall/multiple_functions.sol
    function multipleFunctions() public pure {
        uint ra = retA();
        uint rb = retB();
        uint rc = retC();
        uint rf = retF();
        assert(ra == 0);
        assert(rb == 1);
        assert(rc == 2);
        assert(rf == 3);
    }

    function sumSeq(uint[] memory seqParam) internal pure returns (uint) {
        uint[] memory seq = seqParam;
        uint i = 0;
        uint sum = 0;
        while (i < seq.length)
        {
            uint idx = i;
            if (idx >= 10) break;
            uint v = seq[idx];
            if (v >= 1000) {
                uint n = i + 1;
                i = n;
                continue;
            }
            else {
                uint w = sum + v;
                sum = w;
            }
            if (sum >= 500) return sum;
            i++;
        }
        return sum;
    }

    /// solc: semanticTests/functionCall/array_multiple_local_vars.sol
    function arrayMultipleLocalVars() public pure {
        uint[] memory s1 = new uint[](3);
        s1[0] = 1000;
        s1[1] = 1;
        s1[2] = 2;
        uint r1 = sumSeq(s1);
        assert(r1 == 3);
        uint[] memory s2 = new uint[](3);
        s2[0] = 100;
        s2[1] = 500;
        s2[2] = 300;
        uint r2 = sumSeq(s2);
        assert(r2 == 600);
    }

    /// solc: semanticTests/functionCall/array_multiple_local_vars.sol
    function arrayMultipleLocalVarsBreak() public pure {
        uint[] memory s3 = new uint[](11);
        s3[0] = 1;
        s3[1] = 2;
        s3[2] = 3;
        s3[3] = 4;
        s3[4] = 5;
        s3[5] = 6;
        s3[6] = 7;
        s3[7] = 8;
        s3[8] = 9;
        s3[9] = 10;
        s3[10] = 111;
        uint r3 = sumSeq(s3);
        assert(r3 == 55);
    }

    function exp(uint base, uint exponent) internal pure returns (uint power) {
        if (exponent == 0)
            return 1;
        power = exp(base, exponent / 2);
        power *= power;
        if (exponent % 2 == 1)
            power *= base;
    }

    /// solc: semanticTests/freeFunctions/recursion.sol
    function freeFunctionRecursion() public pure {
        uint e00 = exp(0, 0);
        uint e01 = exp(0, 1);
        uint e10 = exp(1, 0);
        uint e23 = exp(2, 3);
        uint e310 = exp(3, 10);
        assert(e00 == 1);
        assert(e01 == 0);
        assert(e10 == 1);
        assert(e23 == 8);
        assert(e310 == 59049);
    }

    function add(uint p, uint q) internal pure returns (uint) {
        return p + q;
    }

    /// solc: semanticTests/freeFunctions/easy.sol
    function freeFunctionEasy() public pure {
        uint r = add(7, 2);
        assert(r == 9);
    }

    function check(uint v) internal pure {
        assert(v > 0);
    }

    /// solc: smtCheckerTests/functions/free_function_multiple_contracts.sol
    function freeFunctionMultipleContracts() public pure {
        check(1);
    }

    function fun(uint[] memory xParam, uint[] storage yParam) internal view returns (uint, uint[] memory) {
        uint[] storage ys = yParam;
        uint first = ys[0];
        return (first, xParam);
    }

    /// solc: semanticTests/freeFunctions/storage_calldata_refs.sol
    /// @custom:key box
    function storageCalldataRefs() public {
        require(data.length == 0);
        uint[] memory input = new uint[](3);
        input[0] = 8;
        input[1] = 9;
        input[2] = 10;
        data.push(7);
        (uint p, uint[] memory q) = fun(input, data);
        uint q1 = q[1];
        assert(p == 7);
        assert(q1 == 9);
    }

    function lenAndFirst(uint[] memory cParam) internal pure returns (uint p, uint q) {
        uint[] memory c = cParam;
        return (c.length, c[0]);
    }

    /// solc: semanticTests/functionCall/calldata_argument_internal_dynamic_array_v2.sol
    function calldataArgumentInternalDynamicArray() public pure {
        uint[] memory c = new uint[](4);
        c[0] = 1;
        c[1] = 2;
        c[2] = 3;
        c[3] = 4;
        (uint p, uint q) = lenAndFirst(c);
        assert(p == 4);
        assert(q == 1);
    }

    function fields(S memory s) internal pure returns (uint, uint) {
        return (s.x, s.y);
    }

    /// solc: semanticTests/functionCall/calldata_argument_internal_struct_v2.sol
    function calldataArgumentInternalStruct() public pure {
        S memory s;
        s.x = 1;
        s.y = 2;
        (uint p, uint q) = fields(s);
        assert(p == 1);
        assert(q == 2);
    }

    function pick(uint[][] memory sParam) internal pure returns (uint, uint[] memory) {
        uint[][] memory s = sParam;
        uint[] memory s0 = s[0];
        return (s0[1], s[1]);
    }

    /// solc: semanticTests/functionCall/calldata_argument_internal_multi_array_v2.sol
    function calldataArgumentInternalMultiArray() public pure {
        uint[][] memory m = new uint[][](2);
        m[0] = new uint[](2);
        m[1] = new uint[](2);
        m[0][1] = 7;
        m[1][0] = 8;
        (uint p, uint[] memory q) = pick(m);
        uint q0 = q[0];
        assert(p == 7);
        assert(q0 == 8);
    }

    function foo() internal pure returns (uint) {
        return 42;
    }

    /// solc: semanticTests/functionCall/call_internal_function_via_expression.sol
    function callInternalFunctionViaExpression() public pure {
        uint r = (foo)();
        assert(r == 42);
    }

    /// solc: smtCheckerTests/functions/function_inline_chain.sol
    function chainF() public {
        if (y != 1)
            chainG();
        assert(y == 1);
    }

    function chainG() internal {
        y = 1;
        chainH();
    }

    function chainH() internal {
        chainF();
        assert(y == 1);
    }

    function incGuarded() internal {
        require(x < 10000);
        x = x + 1;
    }

    /// solc: smtCheckerTests/functions/function_inside_branch_modify_state_var_2.sol
    function branchModifyStateVarBothBranches(uint flag) public {
        bool bb = flag == 1;
        x = 0;
        if (bb)
            incGuarded();
        else
            incGuarded();
        assert(x == 1);
    }

    /// solc: smtCheckerTests/functions/function_inside_branch_modify_state_var.sol
    function branchModifyStateVarOneBranch(uint flag) public {
        bool bb = flag == 1;
        x = 0;
        if (bb)
            incGuarded();
        if (bb)
            assert(x == 1);
        else
            assert(x == 0);
    }

    function inc() internal returns (uint) {
        require(x < 100);
        return ++x;
    }

    /// solc: smtCheckerTests/functions/functions_identifier_nested_tuple_1.sol
    function identifierNestedTuple() public {
        x = 0;
        ((inc))();
        assert(x == 1);
    }

    function h(uint v) internal pure returns (uint) {
        return v;
    }

    function hk(uint v) internal pure returns (uint) {
        return k(v);
    }

    function k(uint v) internal pure returns (uint) {
        return v;
    }

    /// solc: smtCheckerTests/functions/functions_identity_1.sol
    function functionsIdentity1() public pure {
        uint r;
        r = h(42);
        assert(r > 0);
    }

    /// solc: smtCheckerTests/functions/functions_identity_2.sol
    function functionsIdentity2() public pure {
        uint r;
        r = hk(2);
        assert(r > 0);
    }

    /// solc: smtCheckerTests/functions/functions_identity_as_tuple.sol
    function functionsIdentityAsTuple() public pure {
        uint r;
        r = (h)(42);
        assert(r > 0);
    }

    /// solc: smtCheckerTests/functions/functions_recursive.sol
    function functionsRecursive() public {
        a = 3;
        recursiveG();
    }

    function recursiveG() internal {
        if (a > 0)
        {
            a = a - 1;
            recursiveG();
        }
        else
            assert(a == 0);
    }

    /// solc: smtCheckerTests/functions/functions_recursive_indirect.sol
    function functionsRecursiveIndirect() public {
        a = 3;
        indirectF();
    }

    function indirectF() internal {
        if (a > 0)
        {
            a = a - 1;
            indirectG();
        }
        else
            assert(a == 0);
    }

    function indirectG() internal {
        if (a > 0)
        {
            a = a - 1;
            indirectF();
        }
        else
            assert(a == 0);
    }

    function trivialRequire(bool flag) internal pure {
        require(flag);
    }

    /// solc: smtCheckerTests/functions/functions_trivial_condition_require_only_call.sol
    function trivialConditionRequireOnlyCall() public pure {
        trivialRequire(true);
    }

    function zeroRet() internal pure returns (uint) {}

    /// solc: smtCheckerTests/functions/internal_call_state_var_init.sol
    function internalCallStateVarInit() public pure {
        bool b = (zeroRet() == 0) && (zeroRet() == 0);
        assert(b);
    }

    function incX() internal returns (uint) {
        x = x + 1;
    }

    /// solc: smtCheckerTests/functions/internal_call_state_var_init_2.sol
    function internalCallStateVarInit2() public {
        x = 0;
        bool b = (incX() > 0) || (incX() > 0);
        assert(!b);
        assert(x == 2);
    }

    function decWithAsserts() internal {
        assert(x == 2);
        --x;
        assert(x == 1);
    }

    /// solc: smtCheckerTests/functions/internal_call_with_assertion_1.sol
    function internalCallWithAssertion() public {
        x = 1;
        assert(x == 1);
        ++x;
        decWithAsserts();
        assert(x == 1);
    }

    function dec() internal {
        --x;
    }

    /// solc: smtCheckerTests/functions/internal_multiple_calls_with_assertion_1.sol
    function internalMultipleCallsWithAssertion() public {
        x = 1;
        assert(x == 1);
        ++x;
        ++x;
        dec();
        dec();
        assert(x == 1);
    }

    function addBounded(uint p, uint q) internal pure returns (uint) {
        require(p < 1000);
        require(q < 1000);
        return p + q;
    }

    /// solc: smtCheckerTests/functions/functions_library_1.sol
    /// @custom:key box
    function functionsLibrary1(uint v) public pure {
        uint w = addBounded(v, 999);
        assert(w < 10000);
    }

    /// solc: semanticTests/functionCall/named_args.sol
    function namedArgsUnordered() public pure {
        uint internalUnordered = internalFunction({q: 2, s: 3, p: 1});
        uint publicUnordered = publicFunction({q: 2, s: 3, p: 1});
        assert(internalUnordered == 123);
        assert(publicUnordered == 123);
    }

    /// solc: semanticTests/functionCall/disordered_named_args.sol
    function disorderedNamedArgs() public pure {
        uint r = publicFunction({s: 3, p: 1, q: 2});
        assert(r == 123);
    }
}
