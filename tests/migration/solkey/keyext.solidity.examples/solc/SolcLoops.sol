// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SolcLoops {
    uint[][] array2d;
    struct Data {
        uint x;
        uint y;
    }

    uint sx;
    uint sy;
    uint[] storageArray;
    uint[] dynamic;
    Data[] data;
    uint[] ids;

    /// solc: statements/empty_for_loop.sol
    function emptyForLoopBreaksAtTen() public pure {
        uint ret = 1;
        for (;;) {
            ret += 1;
            if (ret >= 10) break;
        }
        assert(ret == 10);
    }

    /// solc: viaYul/loops/simple.sol
    function forLoopDoubles() public pure {
        uint x = 1;
        for (uint a = 0; a < 10; a = a + 1) {
            x = x + x;
        }
        assert(x == 1024);
    }

    /// solc: viaYul/loops/simple.sol
    function whileLoopDoubles() public pure {
        uint x = 1;
        uint a = 0;
        while (a < 10) {
            x = x + x;
            a = a + 1;
        }
        assert(x == 1024);
    }

    /// solc: viaYul/loops/simple.sol
    function doWhileRunsUntilConditionFails() public pure {
        uint x = 1;
        do {
            x = x + 1;
        } while (x < 3);
        assert(x == 3);
    }

    /// solc: viaYul/loops/break.sol
    function forBreakAfterFirstIteration() public pure {
        uint x = 1;
        for (uint a = 0; a < 10; a = a + 1) {
            x = x + x;
            break;
        }
        assert(x == 2);
    }

    /// solc: viaYul/loops/break.sol
    function whileBreakSkipsRestOfBody() public pure {
        uint x = 1;
        uint a = 0;
        while (a < 10) {
            x = x + x;
            break;
            a = a + 1;
        }
        assert(x == 2);
        assert(a == 0);
    }

    /// solc: viaYul/loops/break.sol
    function doWhileBreakSkipsCondition() public pure {
        uint x = 1;
        do {
            x = x + 1;
            break;
        } while (x < 3);
        assert(x == 2);
    }

    /// solc: viaYul/loops/continue.sol
    function forContinueRunsUpdate() public pure {
        uint x = 1;
        uint a = 0;
        for (; a < 10; a = a + 1) {
            continue;
            x = x + x;
        }
        x = x + a;
        assert(x == 11);
    }

    /// solc: viaYul/loops/continue.sol
    function whileContinueSkipsRestOfBody() public pure {
        uint x = 1;
        uint a = 0;
        while (a < 10) {
            a = a + 1;
            continue;
            x = x + x;
        }
        x = x + a;
        assert(x == 11);
    }

    /// solc: viaYul/loops/continue.sol
    function doWhileContinueEvaluatesCondition() public pure {
        uint x = 1;
        uint a = 0;
        do {
            a = a + 1;
            continue;
            x = x + x;
        } while (a < 4);
        x = x + a;
        assert(x == 5);
    }

    function returnInsideFor() internal pure returns (uint x) {
        x = 1;
        uint a = 0;
        for (; a < 10; a = a + 1) {
            return x;
            x = x + x;
        }
        x = x + a;
    }

    function returnInsideWhile() internal pure returns (uint x) {
        x = 1;
        uint a = 0;
        while (a < 10) {
            return x;
            x = x + x;
            a = a + 1;
        }
        x = x + a;
    }

    function returnInsideDoWhile() internal pure returns (uint x) {
        x = 1;
        do {
            x = x + 1;
            return x;
        } while (x < 3);
    }

    /// solc: viaYul/loops/return.sol
    function returnLeavesLoop() public pure {
        uint f = returnInsideFor();
        uint g = returnInsideWhile();
        uint h = returnInsideDoWhile();
        assert(f == 1);
        assert(g == 1);
        assert(h == 2);
    }

    function ifInsideDoWhileOnce(uint a, uint b2) internal pure returns (uint x, uint y) {
        x = 42;
        do {
            if (a + b2 < 10) {
                if (a == b2) {
                    x = 99;
                    y = 99;
                    break;
                } else {
                    x = a;
                }
            } else {
                x = b2;
                if (a != b2)
                    y = 17;
                else
                    y = 13;
                break;
            }
            y = 100;
        } while (false);
    }

    /// solc: viaYul/if.sol
    function breakOutOfDoWhileFalseSmallSums() public pure {
        (uint x1, uint y1) = ifInsideDoWhileOnce(1, 3);
        assert(x1 == 1);
        assert(y1 == 100);
        (uint x2, uint y2) = ifInsideDoWhileOnce(3, 1);
        assert(x2 == 3);
        assert(y2 == 100);
        (uint x3, uint y3) = ifInsideDoWhileOnce(3, 3);
        assert(x3 == 99);
        assert(y3 == 99);
    }

    /// solc: viaYul/if.sol
    function breakOutOfDoWhileFalseLargeSums() public pure {
        (uint x1, uint y1) = ifInsideDoWhileOnce(10, 23);
        assert(x1 == 23);
        assert(y1 == 17);
        (uint x2, uint y2) = ifInsideDoWhileOnce(23, 10);
        assert(x2 == 10);
        assert(y2 == 17);
        (uint x3, uint y3) = ifInsideDoWhileOnce(23, 23);
        assert(x3 == 23);
        assert(y3 == 13);
    }

    function evenStep(uint x) internal pure returns (uint y) {
        return x / 2;
    }

    function oddStep(uint x) internal pure returns (uint y) {
        return 3 * x + 1;
    }

    function collatz(uint x) internal pure returns (uint y) {
        y = x;
        while (y > 1) {
            if (x % 2 == 0) x = evenStep(x);
            else x = oddStep(x);
            y = x;
        }
    }

    /// solc: functionCall/calling_other_functions.sol
    function collatzReachesOne() public pure {
        uint r0 = collatz(0);
        uint r1 = collatz(1);
        uint r2 = collatz(2);
        uint r8 = collatz(8);
        assert(r0 == 0);
        assert(r1 == 1);
        assert(r2 == 1);
        assert(r8 == 1);
    }

    /// solc: array/array_storage_index_boundary_test.sol
    function boundaryTestPushedSlotsAreZero() public {
        delete storageArray;
        uint len = 10;
        while (storageArray.length < len)
            storageArray.push();
        while (storageArray.length > len)
            storageArray.pop();
        uint l = storageArray.length;
        uint r = storageArray[9];
        assert(l == 10);
        assert(r == 0);
    }

    /// solc: array/dynamic_array_cleanup.sol
    function fillThenHalfClear() public {
        delete dynamic;
        /// @custom:key invariant 0 <= i && i <= 21 && dynamic.length == i
        /// @custom:key invariant \forall uint q; 0 <= q && q < i -> dynamic[q] == q + 1
        /// @custom:key decreases 21 - i
        for (uint i = 0; i < 21; ++i)
            dynamic.push(i + 1);
        /// @custom:key invariant 5 <= dynamic.length && dynamic.length <= 21
        /// @custom:key invariant \forall uint q; 0 <= q && q < dynamic.length -> dynamic[q] == q + 1
        /// @custom:key decreases dynamic.length
        while (dynamic.length > 5)
            dynamic.pop();
        uint l = dynamic.length;
        uint r = dynamic[4];
        assert(l == 5);
        assert(r == 5);
        delete dynamic;
        uint e = dynamic.length;
        assert(e == 0);
    }

    /// solc: array/array_memory_index_access.sol
    function memoryArrayLoopWriteRead() public pure {
        uint len = 10;
        uint[] memory array = new uint[](len);
        for (uint i = 0; i < len; i++)
            array[i] = i + 1;
        for (uint i = 0; i < len; i++)
            require(array[i] == i + 1);
        uint l = array.length;
        uint r = array[1];
        assert(l == len);
        assert(r == 2);
    }

    /// solc: array/array_2d_new.sol
    /// @custom:key box
    function newInnerArraysInLoop(uint n) public pure {
        require(n == 42);
        uint[][] memory a = new uint[][](2);
        for (uint i = 0; i < 2; ++i)
            a[i] = new uint[](3);
        a[0][0] = n;
        uint r = a[0][0];
        uint z = a[1][2];
        assert(r == 42);
        assert(z == 0);
    }

    /// solc: smtCheckerTests/loops/do_while_1.sol
    /// @custom:key box
    function doWhileLeavesPositive(uint x) public pure {
        require(x >= 0 && x < 100);
        /// @custom:key invariant 0 <= x
        do {
            x = x + 1;
        } while (x < 1000);
        assert(x > 0);
    }

    /// solc: smtCheckerTests/loops/do_while_break_2.sol
    function innerDoWhileBreakLeavesOuterBody() public pure {
        uint a = 0;
        while (true) {
            do {
                break;
                a = 2;
            } while (true);
            a = 1;
            break;
        }
        assert(a == 1);
    }

    /// solc: smtCheckerTests/loops/for_1_continue.sol
    /// @custom:key box
    function forContinueRunsIncrement(uint x, uint bb) public pure {
        require(x >= 0 && x < 10 && bb <= 1);
        bool b = bb == 1;
        /// @custom:key invariant 0 <= x
        for (; x < 10; ++x) {
            if (b) {
                x = 20;
                continue;
            }
        }
        assert(x > 0);
    }

    /// solc: smtCheckerTests/loops/for_break_direct.sol
    function forBreakDirectKeepsInit() public pure {
        uint x;
        for (x = 0; x < 10; ++x)
            break;
        assert(x == 0);
    }

    /// solc: smtCheckerTests/loops/for_loop_2.sol
    /// @custom:key box
    function forConditionHoldsInBody(uint x) public pure {
        require(x >= 0);
        /// @custom:key invariant true
        for (; x == 2; ) {
            assert(x == 2);
        }
    }

    /// solc: smtCheckerTests/loops/while_loop_simple_2.sol
    /// @custom:key box
    function whileConditionHoldsInBody(uint x) public pure {
        require(x >= 0);
        /// @custom:key invariant true
        while (x == 2) {
            assert(x == 2);
        }
    }

    /// solc: smtCheckerTests/loops/while_loop_simple_4.sol
    /// @custom:key box
    function whileExitNegatesCondition(uint x) public pure {
        require(x >= 0);
        /// @custom:key invariant true
        while (x == 2) {
        }
        assert(x != 2);
    }

    /// solc: smtCheckerTests/loops/while_1.sol
    /// @custom:key box
    function whileResetOrIncrement(uint x, uint bb) public pure {
        require(x >= 0 && x < 100 && bb <= 1);
        bool b = bb == 1;
        /// @custom:key invariant 0 <= x && x < 100
        while (x < 10) {
            if (b)
                x = x + 1;
            else
                x = 0;
        }
        assert(x > 0);
    }

    /// solc: smtCheckerTests/loops/while_1_continue.sol
    /// @custom:key box
    function whileContinueOrIncrement(uint x, uint bb) public pure {
        require(x >= 0 && x < 10 && bb <= 1);
        bool b = bb == 1;
        /// @custom:key invariant (0 <= x && x <= 10) || x == 20
        while (x < 10) {
            if (b) {
                x = 20;
                continue;
            }
            ++x;
        }
        assert(x >= 10);
    }

    /// solc: smtCheckerTests/loops/while_2.sol
    function whileCountsDownToOne() public pure {
        uint x;
        x = 2;
        while (x > 1) {
            if (x > 10)
                x = 2;
            else
                --x;
        }
        assert(x < 2);
    }

    /// solc: smtCheckerTests/loops/while_2_break.sol
    function whileBreakAfterIncrement() public pure {
        uint x = 0;
        while (x == 0) {
            ++x;
            break;
            ++x;
        }
        assert(x == 1);
    }

    /// solc: smtCheckerTests/loops/while_break_direct.sol
    function whileBreakDirect() public pure {
        uint x;
        x = 0;
        while (x < 10)
            break;
        assert(x == 0);
    }

    /// solc: smtCheckerTests/loops/do_while_bmc_iterations_nested_break.sol
    /// @custom:key box
    function nestedDoWhileBreak(uint z) public pure {
        uint x = 0;
        require(z == 0);
        do {
            uint y = 0;
            do {
                if (y > 0)
                    break;
                ++z;
                ++y;
            } while (y < 2);
            ++x;
        } while (x < 2);
        assert(z == 2);
    }

    /// solc: smtCheckerTests/loops/do_while_bmc_iterations_nested_continue.sol
    /// @custom:key box
    function nestedDoWhileContinue(uint z) public pure {
        uint x = 0;
        require(z == 0);
        do {
            uint y = 0;
            do {
                ++y;
                if (y > 0)
                    continue;
                ++z;
            } while (y < 2);
            ++x;
        } while (x < 2);
        assert(z == 0);
    }

    function condition() private returns (bool) {
        ++sx;
        return sx < 3;
    }

    function expression() private {
        ++sy;
    }

    /// solc: smtCheckerTests/loops/for_loop_bmc_iterations_8.sol
    /// @custom:key box
    function forCallsInConditionAndUpdate() public {
        require(sx == 0);
        require(sy == 0);
        for (; condition(); expression()) {
        }
        assert(sx == 3);
        assert(sy == 2);
    }

    function toggle() private returns (bool) {
        sx = (sx + 1) % 2;
        return (sx == 1);
    }

    /// solc: smtCheckerTests/loops/while_bmc_iterations_6.sol
    /// @custom:key box
    function whileToggleConditionRunsOnce() public {
        require(sx == 0);
        require(sy == 0);
        while (toggle()) {
            ++sy;
        }
        assert(sy == 1);
    }

    /// solc: smtCheckerTests/loops/do_while_bmc_iterations_6.sol
    /// @custom:key box
    function doWhileToggleConditionRunsTwice() public {
        require(sx == 0);
        require(sy == 0);
        do {
            ++sy;
        } while (toggle());
        assert(sy == 2);
    }

    /// solc: smtCheckerTests/loops/for_loop_bmc_iterations_break_continue_3.sol
    function forContinueThenBreak() public pure {
        uint x;
        for (uint i = 0; i < 3; ++i) {
            if (i > 0) {
                x = 1;
                break;
            } else {
                x = 2;
                continue;
            }
        }
        assert(x == 1);
    }

    /// solc: array/array_3d_new.sol
    /// @custom:key box
    function nestedLoopsAllocate3d(uint n) public pure {
        require(n == 42);
        uint[][][] memory a = new uint[][][](2);
        for (uint i = 0; i < 2; ++i)
        {
            a[i] = new uint[][](3);
            for (uint j = 0; j < 3; ++j)
                a[i][j] = new uint[](4);
        }
        a[1][1][1] = n;
        uint r = a[1][1][1];
        assert(r == 42);
    }

    /// solc: array/array_3d_assignment.sol
    /// @custom:key box
    function nestedLoopsAllocate3dThenAlias(uint n) public pure {
        require(n == 42);
        uint[][][] memory a = new uint[][][](2);
        for (uint i = 0; i < 2; ++i)
        {
            a[i] = new uint[][](3);
            for (uint j = 0; j < 3; ++j)
                a[i][j] = new uint[](4);
        }
        a[1][1][1] = n;
        uint[][] memory b = a[1];
        uint[] memory c = b[1];
        uint r = c[1];
        assert(r == 42);
    }

    function receiver(uint[] memory param, uint idx) internal pure returns (uint256) {
        uint[] memory array = param;
        for (uint256 i = 0; i < array.length; i++)
            array[i] = i + 1;
        return array[idx];
    }

    /// solc: array/array_memory_as_parameter.sol
    /// @custom:key box
    function loopFillsMemoryParameter(uint len, uint idx) public pure {
        require(len == 10 && idx == 5);
        uint[] memory array = new uint[](len);
        uint result = receiver(array, idx);
        for (uint256 i = 0; i < array.length; i++)
            require(array[i] == i + 1);
        assert(result == 6);
    }

    /// solc: smtCheckerTests/loops/do_while_break.sol
    function doWhileBreakSkipsAssignment() public pure {
        uint x;
        do {
            break;
            x = 1;
        } while (x == 0);
        assert(x == 0);
    }

    /// solc: smtCheckerTests/loops/while_bmc_iterations_nested_continue.sol
    function nestedWhileContinueSkipsCount() public pure {
        uint x = 0;
        uint i = 0;
        while (i < 3) {
            ++i;
            uint j = 0;
            while (j < 3) {
                ++j;
                if (i > 1)
                    continue;
                ++x;
            }
        }
        assert(x == 3);
    }

    function binomial(uint256 n, uint256 k) internal pure returns (uint256) {
        uint256 size = n + 1;
        uint256[][] memory rows = new uint256[][](size);
        for (uint256 i = 1; i <= n; i++) {
            rows[i] = new uint256[](i);
            rows[i][rows[i].length - 1] = 1;
            rows[i][0] = 1;
            for (uint256 j = 1; j < i - 1; j++)
                rows[i][j] = rows[i - 1][j - 1] + rows[i - 1][j];
        }
        return rows[n][k - 1];
    }

    /// solc: array/memory_arrays_of_various_sizes.sol
    function binomialRowsSmall() public pure {
        uint r = binomial(3, 1);
        assert(r == 1);
    }

    /// solc: array/dynamic_arrays_in_storage.sol
    /// @custom:key box
    function setLengthsByPushLoops(uint l1, uint l2) public {
        require(l1 == 48 && l2 == 49);
        require(data.length == 0);
        require(ids.length == 0);
        /// @custom:key invariant 0 <= data.length && data.length <= 48 && ids.length == 0
        while (data.length < l1) data.push();
        /// @custom:key invariant 0 <= ids.length && ids.length <= 49 && data.length == 48
        while (ids.length < l2) ids.push();
        ids[2] = 11;
        ids[7] = 8;
        data[7].x = 8;
        data[7].y = 9;
        data[8].x = 10;
        data[8].y = 11;
        uint n1 = data.length;
        uint n2 = ids.length;
        uint i2 = ids[2];
        uint i7 = ids[7];
        uint x7 = data[7].x;
        uint y7 = data[7].y;
        uint x8 = data[8].x;
        uint y8 = data[8].y;
        assert(n1 == 48);
        assert(n2 == 49);
        assert(i2 == 11);
        assert(i7 == 8);
        assert(x7 == 8);
        assert(y7 == 9);
        assert(x8 == 10);
        assert(y8 == 11);
    }

    function stepCondition() private returns (bool) {
        ++sx;
        return sx < 3;
    }

    /// solc: smtCheckerTests/loops/for_loop_bmc_iterations_7.sol
    /// @custom:key box
    function forConditionCallRunsThrice() public {
        require(sx == 0);
        for (; stepCondition();) {
        }
        assert(sx == 3);
    }

    /// solc: smtCheckerTests/loops/do_while_bmc_iterations_5.sol
    /// @custom:key box
    function doWhileConditionCallRunsThrice() public {
        require(sx == 0);
        do {
        } while (stepCondition());
        assert(sx == 3);
    }

    /// solc: smtCheckerTests/loops/do_while_bmc_iterations_break_continue_2.sol
    function doWhileContinueThenBreak() public pure {
        uint x = 0;
        do {
            if (x > 1) {
                x = 3;
                break;
            }
            if (x >= 0) {
                x = 2;
                continue;
            }
        } while (x < 4);
        assert(x == 3);
    }

    /// solc: smtCheckerTests/loops/for_loop_bmc_iterations_break_5.sol
    function forSecondBreakUnreachable() public pure {
        uint x = 0;
        for (uint i = 0; i < 3; ++i) {
            if (i > 1) {
                x = 1;
                break;
            }
            if (i > 1) {
                x = 2;
                break;
            }
        }
        assert(x == 1);
    }

    /// solc: smtCheckerTests/loops/for_loop_bmc_iterations_continue_4.sol
    function forContinueRunsUpdateAfterReassign() public pure {
        uint x = 0;
        for (; x < 2; ++x) {
            if (x > 1) {
                x = 10;
                continue;
            }
            if (x > 0) {
                x = 11;
                continue;
            }
        }
        assert(x == 12);
    }

    /// solc: smtCheckerTests/loops/for_loop_bmc_iterations_shallow_unroll.sol
    function forShallowUnrollAssertIsFalse() public pure {
        uint x = 0;
        for (uint i = 0; i < 2; ++i) {
            ++x;
        }
        assert(x != 3);
    }

    /// solc: array/push/push_no_args_2d.sol
    /// @custom:key box
    function pushChainedAssign(uint value) public {
        require(value == 512);
        require(array2d.length == 0);
        array2d.push().push() = value;
        uint a = array2d[0][0];
        assert(a == 512);
    }

    /// solc: smtCheckerTests/loops/for_1_break.sol
    /// @custom:key box
    function forBreakOrIncrement(uint x, uint bb) public pure {
        require(x >= 0 && x < 10 && bb <= 1);
        bool b = bb == 1;
        /// @custom:key invariant (0 <= x && x <= 10) || x == 20
        for (; x < 10; ) {
            if (b)
                ++x;
            else {
                x = 20;
                break;
            }
        }
        assert(x >= 10);
    }

    /// solc: smtCheckerTests/loops/while_1_break.sol
    /// @custom:key box
    function whileBreakOrIncrement(uint x, uint bb) public pure {
        require(x >= 0 && x < 10 && bb <= 1);
        bool b = bb == 1;
        /// @custom:key invariant (0 <= x && x <= 10) || x == 20
        while (x < 10) {
            if (b)
                ++x;
            else {
                x = 20;
                break;
            }
        }
        assert(x >= 10);
    }

    /// solc: smtCheckerTests/loops/while_nested_break.sol
    /// @custom:key box
    function nestedWhileBreak(uint x, uint y, uint bb, uint cc) public pure {
        require(x >= 0 && x < 10 && y >= 0 && bb <= 1 && cc <= 1);
        bool b = bb == 1;
        bool c = cc == 1;
        /// @custom:key invariant ((0 <= x && x < 10) || x == 15) && y >= 0
        while (x < 10) {
            if (b) {
                ++x;
                if (x == 10)
                    x = 15;
            }
            else {
                require(y < 10);
                /// @custom:key invariant (0 <= y && y <= 10) || y == 20
                while (y < 10) {
                    if (c)
                        ++y;
                    else {
                        y = 20;
                        break;
                    }
                }
                assert(y >= 10);
                x = 15;
                break;
            }
        }
        assert(x >= 15);
    }

    /// solc: smtCheckerTests/loops/while_nested_continue.sol
    /// @custom:key box
    function nestedWhileContinue(uint x, uint y, uint bb, uint cc) public pure {
        require(x >= 0 && x < 10 && y >= 0 && bb <= 1 && cc <= 1);
        bool b = bb == 1;
        bool c = cc == 1;
        /// @custom:key invariant ((0 <= x && x < 10) || x >= 15) && y >= 0
        while (x < 10) {
            if (b) {
                x = 20;
                continue;
            }
            else {
                require(y < 10);
                /// @custom:key invariant (0 <= y && y < 10) || y == 15 || y == 20
                while (y < 10) {
                    if (c) {
                        y = 20;
                        continue;
                    }
                    y = 15;
                    break;
                }
                assert(y >= 15);
                x = y;
            }
        }
        assert(x >= 15);
    }

}
