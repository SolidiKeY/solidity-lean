// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SolcLoopsOpen {
    struct Nest {
        uint[][] d;
    }

    uint[][] array2d;
    Nest[] nests;

    // open: the invariant cannot name the lowered break flag, so the exit by break keeps x in [0, 10)
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

    // open: the invariant cannot name the lowered break flag, so the exit by break keeps x in [0, 10)
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

    // open: the invariant cannot name the lowered break flag of the inner loop
    /// solc: smtCheckerTests/loops/while_nested_break.sol
    /// @custom:key box
    function nestedWhileBreak(uint x, uint y, uint bb, uint cc) public pure {
        require(x >= 0 && x < 10 && y >= 0 && bb <= 1 && cc <= 1);
        bool b = bb == 1;
        bool c = cc == 1;
        /// @custom:key invariant (0 <= x && x < 10) || x == 15
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

    // open: the invariant cannot name the lowered break flag of the inner loop
    /// solc: smtCheckerTests/loops/while_nested_continue.sol
    /// @custom:key box
    function nestedWhileContinue(uint x, uint y, uint bb, uint cc) public pure {
        require(x >= 0 && x < 10 && y >= 0 && bb <= 1 && cc <= 1);
        bool b = bb == 1;
        bool c = cc == 1;
        /// @custom:key invariant (0 <= x && x < 10) || x >= 15
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

    function binomialFaithful(uint256 n, uint256 k) internal pure returns (uint256) {
        uint256[][] memory rows = new uint256[][](n + 1);
        for (uint256 i = 1; i <= n; i++) {
            rows[i] = new uint256[](i);
            rows[i][0] = rows[i][rows[i].length - 1] = 1;
            for (uint256 j = 1; j < i - 1; j++)
                rows[i][j] = rows[i - 1][j - 1] + rows[i - 1][j];
        }
        return rows[n][k - 1];
    }

    // open: new uint256[][](n + 1) with a non-simple length is stuck on the program text
    /// solc: array/memory_arrays_of_various_sizes.sol
    function binomialFaithfulRowsSmall() public pure {
        uint r = binomialFaithful(3, 1);
        assert(r == 1);
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

    // open: nested memory rows: does not close within the default budget, nor with -m 1000000
    /// solc: array/memory_arrays_of_various_sizes.sol
    function binomialRowsNine() public pure {
        uint r = binomial(9, 5);
        assert(r == 70);
    }

    // open: nested push loops exceed the suite budget of 50000 steps / 30 s
    /// solc: array/dynamic_multi_array_cleanup.sol
    /// @custom:key box
    function multiArrayFillByPushLoops() public {
        require(nests.length == 0);
        while (nests.length < 3)
            nests.push();
        while (nests[2].d.length < 4)
            nests[2].d.push();
        while (nests[2].d[3].length < 5)
            nests[2].d[3].push();
        nests[2].d[3][4] = 8;
        uint r = nests[2].d[3][4];
        assert(r == 8);
        delete nests;
        uint l = nests.length;
        assert(l == 0);
    }

    // open: unrolling 43 pushes exceeds the suite budget of 50000 steps / 30 s
    /// solc: array/push/push_no_args_2d.sol
    /// @custom:key box
    function pushNoArgs2dLoop(uint index, uint value) public {
        require(index == 42 && value == 64);
        require(array2d.length == 0);
        uint[] storage pointer = array2d.push();
        for (uint i = 0; i <= index; ++i)
            pointer.push();
        pointer[index] = value;
        uint l = array2d.length;
        uint ll = array2d[0].length;
        uint a = array2d[0][42];
        assert(l == 1);
        assert(ll == 43);
        assert(a == 64);
    }

}
