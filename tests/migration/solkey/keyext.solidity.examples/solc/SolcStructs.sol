// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of `test/libsolidity/semanticTests/structs/` from the solc compiler test suite. Each
/// function names the upstream file it comes from; upstream `constructor` bodies and state
/// initializers become plain assignments, and the `// f() -> v` expectation becomes an in-body
/// `assert` (see `keyext.solidity.examples/solc/README.md`).
///
/// Symbolic execution starts from unconstrained storage, so wherever upstream relies on
/// storage being zero-initialized the assumption is stated with a `require` and the function is
/// box-tagged.
contract SolcStructs {
    struct Simple { uint value; }
    struct Pair { uint a; uint b; }
    struct WithArray { uint n; uint[] items; }
    struct Triple { uint x; uint y; uint z; }
    struct Flagged { uint x; bool y; }

    struct s2 { uint z; Flagged flagged; mapping(uint => s2) recursive; }

    Simple data1;
    WithArray withArray;
    Triple triple;
    uint neighbourBefore;
    uint neighbourAfter;
    s2 data;
    s2 nested;
    Pair source;
    Pair target;
    Pair[] pairs1;
    Pair[] pairs2;
    mapping(uint => Simple) campaigns;

    /// solc: structs/struct_delete_member.sol — `T storage x = data1;` does not copy: writing
    /// and then deleting through `x` is observable on `data1`.
    function deleteMemberThroughStorageAlias() public {
        data1.value = 2;
        Simple storage x = data1;
        x.value = 4;
        delete x.value;
        assert(data1.value == 0);
    }

    /// solc: structs/struct_delete_storage.sol — `delete s` resets every member of the struct
    /// and leaves the neighbouring state variables alone.
    function deleteStructLeavesNeighbours() public {
        neighbourBefore = 23;
        neighbourAfter = 17;
        triple.x = 42;
        triple.y = 42;
        triple.z = 42;
        delete triple;
        assert(triple.x == 0);
        assert(triple.y == 0);
        assert(triple.z == 0);
        assert(neighbourBefore == 23);
        assert(neighbourAfter == 17);
    }

    /// solc: structs/struct_delete_storage_with_array.sol — `delete s` on a struct holding a
    /// dynamic array resets the array's length.
    /// @custom:key box
    function deleteStructResetsArrayLength() public {
        require(withArray.items.length == 2);
        delete withArray;
        uint len = withArray.items.length;
        assert(len == 0);
    }

    /// solc: structs/struct_delete_struct_in_mapping.sol — `delete m[k]` resets the whole
    /// entry.
    function deleteStructInMapping() public {
        campaigns[0].value = 2;
        delete campaigns[0];
        assert(campaigns[0].value == 0);
    }

    /// solc: structs/struct_delete_struct_in_mapping.sol — the entry next to the deleted one
    /// is untouched.
    function deleteEntryKeepsOtherKeys() public {
        campaigns[0].value = 2;
        campaigns[1].value = 3;
        delete campaigns[0];
        assert(campaigns[0].value == 0);
        assert(campaigns[1].value == 3);
    }

    /// solc: structs/struct_reference.sol — a mapping alias and a struct alias taken out of it
    /// both write through to the original path.
    ///
    /// A mapping that is a struct *member* has to be bound to an alias before it can be
    /// indexed: `data.recursive[0].z` leaves an open goal where `map[0].z` closes (README,
    /// "Deviations").
    /// @custom:key box
    function recursiveStructThroughAliases() public {
        mapping(uint => s2) storage map = data.recursive;
        s2 storage inner = map[0];
        mapping(uint => s2) storage innerMap = inner.recursive;
        require(innerMap[1].z == 0);
        data.z = 2;
        inner.z = 3;
        uint prev = innerMap[1].z;
        innerMap[0].z = prev + 1;
        assert(data.z == 2);
        assert(map[0].z == 3);
        assert(innerMap[1].z == 0);
        assert(innerMap[0].z == 1);
    }

    /// solc: structs/structs.sol — the upstream `set()`/`check()` pair over a struct that
    /// nests both a plain struct and a recursive mapping; every write is independent. One
    /// alias per member mapping, as in [recursiveStructThroughAliases].
    function nestedRecursiveStructSetAndCheck() public {
        mapping(uint => s2) storage map = nested.recursive;
        s2 storage third = map[3];
        mapping(uint => s2) storage thirdMap = third.recursive;
        s2 storage fourth = map[4];
        mapping(uint => s2) storage fourthMap = fourth.recursive;
        nested.z = 1;
        nested.flagged.x = 2;
        nested.flagged.y = true;
        thirdMap[4].z = 5;
        fourthMap[3].z = 6;
        map[0].flagged.y = false;
        map[4].z = 9;
        assert(nested.z == 1);
        assert(nested.flagged.x == 2);
        assert(nested.flagged.y == true);
        assert(thirdMap[4].z == 5);
        assert(fourthMap[3].z == 6);
        assert(map[0].flagged.y == false);
        assert(map[4].z == 9);
    }

    /// solc: structs/struct_copy_via_local.sol — a storage struct copied out to memory and
    /// back into another storage struct keeps every member.
    function structCopyViaMemoryLocal() public {
        source.a = 1;
        source.b = 2;
        Pair memory x = source;
        target = x;
        assert(target.a == 1);
        assert(target.b == 2);
    }

    /// solc: structs/copy_from_storage.sol — the storage source is copied, not aliased: a
    /// later write to the source does not reach the copy.
    function structCopyFromStorageIsDeep() public {
        source.a = 13;
        source.b = 14;
        target = source;
        source.a = 20;
        source.b = 21;
        assert(target.a == 13);
        assert(target.b == 14);
    }

    /// solc: array/copying/array_copy_storage_storage_struct.sol — the element-wise form of
    /// the upstream whole-array copy `data2 = data1;` (which has no terminal rule yet).
    /// @custom:key box
    function structArrayElementCopy() public {
        require(pairs1.length == 0);
        require(pairs2.length == 0);
        pairs1.push();
        pairs2.push();
        pairs1[0].a = 4;
        pairs1[0].b = 5;
        Pair storage src = pairs1[0];
        pairs2[0] = src;
        assert(pairs2[0].a == 4);
        assert(pairs2[0].b == 5);
    }

    /// solc: array/copying/array_copy_storage_storage_struct.sol — the same copy performed
    /// member by member through two element aliases.
    /// @custom:key box
    function structArrayElementCopyMemberwise() public {
        require(pairs1.length == 0);
        require(pairs2.length == 0);
        pairs1.push();
        pairs2.push();
        pairs1[0].a = 4;
        pairs1[0].b = 5;
        Pair storage src = pairs1[0];
        Pair storage dst = pairs2[0];
        dst.a = src.a;
        dst.b = src.b;
        assert(pairs2[0].a == 4);
        assert(pairs2[0].b == 5);
    }
}
