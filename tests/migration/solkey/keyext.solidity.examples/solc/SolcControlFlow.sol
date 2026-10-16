// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of the control-flow tests of the solc compiler test suite:
/// `semanticTests/statements/`, `semanticTests/various/swap_in_storage_overwrite.sol` and
/// `semanticTests/expressions/conditional_expression_storage_memory_*.sol`.
///
/// A parameter must be integer-typed for an obligation to be generated, so upstream's
/// `f(bool cond)` becomes `f(uint cond)` with the flag derived in the body.
contract SolcControlFlow {
    struct Pair { uint a; uint b; }

    Pair sx;
    Pair sy;
    Pair target;
    uint[] values;

    /// solc: statements/do_while_loop_continue.sol — `do { … } while (false)` runs its body
    /// exactly once: the guard `i > 0` is false on the only iteration, so the body increments
    /// `i`, and the `continue` it skips would have jumped to the false condition.
    function doWhileFalseRunsBodyOnce() public pure {
        uint i = 0;
        uint r = 0;
        do {
            if (i > 0) continue;
            i = i + 1;
        } while (false);
        r = 42;
        assert(i == 1);
        assert(r == 42);
    }

    /// solc: array/array_storage_index_zeroed_test.sol — the upstream
    /// `for (uint i = 0; i < len; i++) storageArray[i] = i + 1;` at length 3.
    /// @custom:key box
    function forLoopOverArray() public {
        require(values.length == 3);
        uint i;
        for (i = 0; i < values.length; i++) values[i] = i + 1;
        assert(i == 3);
        assert(values[0] == 1);
        assert(values[1] == 2);
        assert(values[2] == 3);
    }

    /// solc: various/swap_in_storage_overwrite.sol — `(x, y) = (y, x)` does not swap. solc
    /// assigns the tuple components with no temporary, so the pair runs as `y = x; x = y;`
    /// and both structs end up holding x's original value. Tuple assignment does not parse
    /// here, so the port is that desugaring.
    function sequentialAssignmentDoesNotSwap() public {
        sx.a = 1;
        sx.b = 2;
        sy.a = 3;
        sy.b = 4;
        sy = sx;
        sx = sy;
        assert(sx.a == 1);
        assert(sx.b == 2);
        assert(sy.a == 1);
        assert(sy.b == 2);
    }

    /// solc: various/swap_in_storage_overwrite.sol — the corrected version, with the temporary
    /// the upstream test shows is necessary.
    function swapViaTemporary() public {
        sx.a = 1;
        sx.b = 2;
        sy.a = 3;
        sy.b = 4;
        Pair memory tmp = sx;
        sx = sy;
        sy = tmp;
        assert(sx.a == 3);
        assert(sx.b == 4);
        assert(sy.a == 1);
        assert(sy.b == 2);
    }

    /// solc: expressions/conditional_expression_storage_memory_1.sol — `data1 = cond ? x : y;`
    /// with two memory sources, `cond` true.
    /// @custom:key box
    function ternarySelectsFirstMemorySource(uint cond) public {
        require(cond == 1);
        bool c = cond == 1;
        Pair memory mx;
        mx.a = 11;
        Pair memory my;
        my.a = 22;
        target = c ? mx : my;
        assert(target.a == 11);
    }

    /// solc: expressions/conditional_expression_storage_memory_2.sol — the upstream
    /// `x = cond ? y : data1;`: the selection goes into a *memory* target, which closes.
    /// @custom:key box
    function ternaryIntoMemoryTarget(uint cond) public pure {
        require(cond == 1);
        bool c = cond == 1;
        Pair memory mx;
        mx.a = 11;
        Pair memory my;
        my.a = 22;
        Pair memory r = c ? mx : my;
        assert(r.a == 11);
    }

    /// solc: expressions/conditional_expression_storage_memory_1.sol — the same selection into
    /// a storage target, written as `if`/`else` instead of `?:`.
    /// @custom:key box
    function ifElseSelectsMemorySource(uint cond) public {
        require(cond == 0);
        bool c = cond == 1;
        Pair memory mx;
        mx.a = 11;
        Pair memory my;
        my.a = 22;
        if (c) {
            target = mx;
        } else {
            target = my;
        }
        assert(target.a == 22);
    }

    /// solc: expressions/conditional_expression_storage_memory_1.sol — the branch selection on
    /// its own, over plain values rather than references.
    /// @custom:key box
    function ternarySelectsValueByFlag(uint cond) public pure {
        require(cond == 0);
        bool c = cond == 1;
        uint r = c ? 11 : 22;
        assert(r == 22);
    }

    /// solc: expressions/conditional_expression_storage_memory_1.sol — the upstream result is
    /// read back through a chain of independent `if`s, the last matching one winning.
    function chainedIfsSelectLastMatch() public {
        target.a = 2;
        uint t = target.a;
        uint r = 0;
        if (t == 1) {
            r = 1;
        }
        if (t == 2) {
            r = 2;
        }
        assert(r == 2);
    }

    /// solc: expressions/conditional_expression_multiple.sol — the same branch structure as a
    /// nested `if`/`else` rather than a nested `?:`.
    /// @custom:key box
    function nestedIfElseSelectsBranch(uint x) public pure {
        require(x == 500);
        uint d = 0;
        if (x > 100) {
            if (x > 1000) {
                d = 1000;
            } else {
                d = 100;
            }
        } else {
            if (x > 50) {
                d = 50;
            } else {
                d = 10;
            }
        }
        assert(d == 100);
    }
}
