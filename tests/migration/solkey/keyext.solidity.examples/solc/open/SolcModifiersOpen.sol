// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of `test/libsolidity/semanticTests/modifiers/` and
/// `test/libsolidity/smtCheckerTests/modifiers/` that load but do not close.
contract SolcModifiersOpen {
    uint x;
    uint a;
    uint[] order;

    modifier m1(uint) { _; }
    modifier m2(uint) { _; }
    modifier m3(uint) { _; }

    modifier namedArg1(uint value) { _; }
    modifier namedArg2(uint value) { _; }

    modifier runBreak() {
        for (uint256 i = 0; i < 10; i++) {
            _;
            if (i == 1)
                break;
        }
    }

    modifier runContinue() {
        for (uint256 i = 0; i < 10; i++) {
            if (i % 2 == 1) continue;
            _;
        }
    }

    modifier repeat(uint256 count) {
        uint256 i;
        for (i = 0; i < count; ++i) _;
    }

    modifier runReturn() {
        for (uint256 i = 1; i < 10; i++) {
            if (i == 5) return;
            _;
        }
    }

    modifier stacked() {
        for (uint256 i = 0; i < 10; i++) {
            _;
            ++x;
            return;
        }
    }

    modifier repeatIf(bool twice) {
        if (twice) _;
        _;
    }

    modifier requireTwoThenReturn(uint u) {
        require(u == 2);
        _;
        return;
    }

    modifier requireThree(uint u) {
        require(u == 3);
        _;
    }

    modifier twoPlaceholders() {
        require(x > 0);
        require(x < 10000);
        _;
        assert(x > 1);
        _;
        assert(x > 2);
    }

    function pushOrder(uint y) internal returns (uint) {
        order.push(y);
        return 0;
    }

    function ordered() internal m2(pushOrder(1)) m1(pushOrder(3)) m3(pushOrder(5)) {
        pushOrder(7);
    }

    function returnsAssigned() internal pure namedArg1(r1 = 2) namedArg2(r2 = 3)
        returns (uint r1, uint r2)
    {
    }

    function incBreak() internal runBreak {
        uint256 k = x;
        uint256 t = k + 1;
        x = t;
    }

    function incContinue() internal runContinue {
        uint256 k = x;
        uint256 t = k + 1;
        x = t;
    }

    function repeated() internal pure repeat(10) returns (uint256 r) {
        r += 1;
    }

    function incUntilReturn() internal runReturn {
        uint256 k = x;
        uint256 t = k + 1;
        x = t;
    }

    function stackedReturn() internal stacked stacked stacked returns (uint) {
        for (uint256 i = 0; i < 10; i++) {
            ++x;
            return 42;
        }
    }

    function repeatedIf(bool twice) internal pure repeatIf(twice) returns (uint256 r) {
        r += 1;
    }

    function repeatedIfReturn(bool twice) internal pure repeatIf(twice) returns (uint256 r) {
        r += 1;
        return r;
    }

    function incTwice() internal twoPlaceholders {
        x = x + 1;
    }

    // open: a function call as a modifier argument stays stuck as an unresolved fn#id(...) declaration
    /// solc: semanticTests/modifiers/evaluation_order.sol
    /// @custom:key box
    function modifierArgumentEvaluationOrder() public {
        require(order.length == 0);
        ordered();
        assert(order.length == 4);
        assert(order[0] == 1);
        assert(order[1] == 3);
        assert(order[2] == 5);
        assert(order[3] == 7);
    }

    // open: an assignment expression used as a modifier argument has no rule
    /// solc: semanticTests/modifiers/function_modifier_return_reference.sol
    function modifierArgumentAssignsReturn() public pure {
        (uint r1, uint r2) = returnsAssigned();
        assert(r1 == 2);
        assert(r2 == 3);
    }

    // open: a for loop in a modifier body is not lowered, so no loop rule matches it
    /// solc: semanticTests/modifiers/break_in_modifier.sol
    function breakInModifier() public {
        x = 0;
        incBreak();
        assert(x == 2);
    }

    // open: a for loop in a modifier body is not lowered, so no loop rule matches it
    /// solc: semanticTests/modifiers/continue_in_modifier.sol
    function continueInModifier() public {
        x = 0;
        incContinue();
        assert(x == 5);
    }

    // open: a for loop in a modifier body is not lowered, so no loop rule matches it
    /// solc: semanticTests/modifiers/function_modifier_loop.sol
    function modifierLoop() public pure {
        uint r = repeated();
        assert(r == 10);
    }

    // open: a modifier containing return is not inlined
    /// solc: semanticTests/modifiers/return_in_modifier.sol
    function returnInModifier() public {
        x = 0;
        incUntilReturn();
        assert(x == 4);
    }

    // open: a modifier containing return is not inlined
    /// solc: semanticTests/modifiers/stacked_return_with_modifiers.sol
    function stackedReturnWithModifiers() public {
        x = 0;
        uint r = stackedReturn();
        assert(r == 42);
        assert(x == 4);
    }

    // open: a modifier with two placeholders is not inlined
    /// solc: semanticTests/modifiers/function_modifier_multi_invocation.sol
    function multiInvocationOnce() public pure {
        uint r = repeatedIf(false);
        assert(r == 1);
    }

    // open: a modifier with two placeholders is not inlined
    /// solc: semanticTests/modifiers/function_modifier_multi_invocation.sol
    function multiInvocationTwice() public pure {
        uint r = repeatedIf(true);
        assert(r == 2);
    }

    // open: a modifier with two placeholders is not inlined
    /// solc: semanticTests/modifiers/function_modifier_multi_with_return.sol
    function multiWithReturnTwice() public pure {
        uint r = repeatedIfReturn(true);
        assert(r == 2);
    }

    // open: a modifier containing return is not inlined
    /// solc: smtCheckerTests/modifiers/modifier_return.sol
    /// @custom:key box
    function smtModifierReturn(uint y) public pure requireTwoThenReturn(y) requireThree(y) {
        assert(y == 3);
    }

    // open: a modifier with two placeholders is not inlined
    /// solc: smtCheckerTests/modifiers/modifier_two_placeholders.sol
    /// @custom:key box
    function smtTwoPlaceholders() public {
        incTwice();
    }
}
