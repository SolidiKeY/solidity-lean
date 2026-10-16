// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of `test/libsolidity/semanticTests/array/` (including `array/push`, `array/pop` and
/// `array/delete`) from the solc compiler test suite. Upstream drives most of these with a
/// `while`/`for` loop over a length parameter; the calculus has no loop rule, so the loops are
/// unrolled to a fixed small length — the semantics under test (what `push` appends, what `pop`
/// leaves behind, which element `delete` resets) does not depend on the bound.
///
/// Symbolic execution starts from unconstrained storage, so the upstream "the array starts
/// empty" premise is stated with `require(arr.length == 0)` and the functions are box-tagged.
contract SolcArrays {
    struct Pair { uint a; uint b; }

    uint[] storageArray;
    uint[][] matrix;
    Pair[] structs;

    /// solc: array/array_push_return_reference.sol — `arr.push() = v;` writes the new slot and
    /// bumps the length; the upstream `fetch(0) -> 42`, `fetch(1) -> 23` sequence.
    /// @custom:key box
    function pushLvalueAssignsAndGrows() public {
        require(storageArray.length == 0);
        storageArray.push() = 42;
        assert(storageArray.length == 1);
        assert(storageArray[0] == 42);
        storageArray.push() = 23;
        assert(storageArray.length == 2);
        assert(storageArray[0] == 42);
        assert(storageArray[1] == 23);
    }

    /// solc: array/array_push_with_arg.sol — `arr.push(v)` appends `v`.
    /// @custom:key box
    function pushWithArgument() public {
        require(storageArray.length == 0);
        storageArray.push(42);
        assert(storageArray.length == 1);
        assert(storageArray[0] == 42);
    }

    /// solc: array/array_storage_push_pop.sol — the upstream `set_get_length` grows the array
    /// with `push()` and drains it with `pop()`, ending at length 0. Unrolled to three.
    /// @custom:key box
    function pushThenPopRestoresLength() public {
        require(storageArray.length == 0);
        storageArray.push();
        storageArray.push();
        storageArray.push();
        assert(storageArray.length == 3);
        storageArray.pop();
        assert(storageArray.length == 2);
        storageArray.pop();
        storageArray.pop();
        assert(storageArray.length == 0);
    }

    /// solc: array/array_storage_push_empty.sol — a no-arg `push()` appends one slot.
    /// @custom:key box
    function pushEmptyGrowsLength() public {
        require(storageArray.length == 2);
        storageArray.push();
        assert(storageArray.length == 3);
    }

    /// solc: array/array_storage_index_zeroed_test.sol — the upstream invariant that a slot
    /// beyond the current length reads as zero: write a slot, pop it, push it back, and it is
    /// cleared.
    /// @custom:key box
    function popThenPushSlotIsZeroed() public {
        require(storageArray.length == 0);
        storageArray.push();
        storageArray[0] = 7;
        assert(storageArray[0] == 7);
        storageArray.pop();
        storageArray.push();
        assert(storageArray[0] == 0);
    }

    /// solc: array/array_storage_index_zeroed_test.sol — the direct form of the same
    /// invariant: a freshly pushed slot reads as zero.
    /// @custom:key box
    function pushedSlotIsZeroed() public {
        require(storageArray.length == 0);
        storageArray.push();
        assert(storageArray[0] == 0);
    }

    /// solc: array/array_storage_index_access.sol — element writes are independent of each
    /// other.
    /// @custom:key box
    function storageIndexReadWrite() public {
        require(storageArray.length == 3);
        storageArray[0] = 1;
        storageArray[1] = 2;
        storageArray[2] = 3;
        assert(storageArray[0] == 1);
        assert(storageArray[1] == 2);
        assert(storageArray[2] == 3);
    }

    /// solc: array/storage_array_ref.sol — `uint[] storage ref = arr;` is a reference, so a
    /// write through it is visible on the original array.
    /// @custom:key box
    function storageArrayAliasWritesThrough() public {
        require(storageArray.length == 2);
        uint[] storage ref = storageArray;
        ref[1] = 33;
        assert(storageArray[1] == 33);
        assert(ref.length == 2);
    }

    /// solc: array/storage_array_ref.sol — the same reference semantics on an array of
    /// structs.
    /// @custom:key box
    function storageStructArrayAliasWritesThrough() public {
        require(structs.length == 2);
        Pair[] storage ref = structs;
        ref[1].a = 33;
        assert(structs[1].a == 33);
        assert(ref.length == 2);
    }

    /// solc: array/delete/delete_on_array_of_structs.sol — `delete arr[i]` resets that element
    /// and leaves its neighbour alone.
    /// @custom:key box
    function deleteArrayElementOfStructs() public {
        require(structs.length == 2);
        structs[0].a = 1;
        structs[0].b = 2;
        structs[1].a = 3;
        structs[1].b = 4;
        delete structs[0];
        assert(structs[0].a == 0);
        assert(structs[0].b == 0);
        assert(structs[1].a == 3);
        assert(structs[1].b == 4);
    }

    /// solc: array/array_2d_assignment.sol — an element of a `uint[][]` is addressed by two
    /// index steps.
    /// @custom:key box
    function matrixElementWriteRead() public {
        require(2 < matrix.length);
        require(3 < matrix[2].length);
        matrix[2][3] = 7;
        uint r = matrix[2][3];
        assert(r == 7);
    }

    /// solc: array/array_storage_length_access.sol — `push` and `pop` are the only things that
    /// change `length`.
    /// @custom:key box
    function lengthTracksPushAndPop() public {
        require(storageArray.length == 1);
        storageArray[0] = 5;
        assert(storageArray.length == 1);
        storageArray.push(6);
        assert(storageArray.length == 2);
        storageArray.pop();
        assert(storageArray.length == 1);
        assert(storageArray[0] == 5);
    }
}
