// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of the memory-location tests of the solc compiler test suite:
/// `semanticTests/structs/memory_structs_*.sol`, `structs/struct_storage_to_memory.sol`,
/// `structs/struct_memory_to_storage.sol`, `array/copying/array_copy_storage_to_memory.sol`
/// and `array/delete/memory_arrays_delete.sol`.
///
/// Upstream reads its results back through return values; here each observed value is bound to
/// a local and stated with `assert`. Fixed-size arrays (`S[5] data`) become dynamic arrays with
/// their length assumed, since the calculus has no fixed-length array type.
contract SolcMemory {
    struct Inner { uint a; uint b; uint c; }
    struct Outer { uint a; Inner s; }
    struct Basket { uint[] items; }

    Outer x;
    Inner inner;
    Inner[] data;
    uint[] prims;

    /// solc: structs/memory_structs_read_write.sol (`testInit`) — a fresh memory struct reads
    /// as all zeros.
    function memoryStructDefaultsToZero() public pure {
        Inner memory d;
        assert(d.a == 0);
        assert(d.b == 0);
        assert(d.c == 0);
    }

    /// solc: structs/memory_structs_read_write.sol (`testAssign`) — member writes on a memory
    /// struct read back.
    function memoryStructWriteRead() public pure {
        Inner memory s;
        s.a = 1;
        s.b = 2;
        s.c = 3;
        assert(s.a == 1);
        assert(s.b == 2);
        assert(s.c == 3);
    }

    /// solc: structs/memory_structs_read_write.sol (`testCopyRead`) — the upstream
    /// `S memory s = data[2];` copy out of a storage array element.
    /// @custom:key box
    function storageArrayElementCopiedIntoMemory() public {
        require(data.length == 3);
        data[2].a = 1;
        data[2].b = 2;
        data[2].c = 3;
        Inner memory s = data[2];
        assert(s.a == 1);
        assert(s.b == 2);
        assert(s.c == 3);
    }

    /// solc: structs/struct_storage_to_memory.sol — the upstream `X memory m = x;` over a
    /// struct that nests another struct.
    function nestedStorageStructToMemory() public {
        x.a = 12;
        x.s.a = 42;
        x.s.b = 23;
        x.s.c = 34;
        Outer memory m = x;
        assert(m.a == 12);
        assert(m.s.a == 42);
        assert(m.s.b == 23);
        assert(m.s.c == 34);
    }

    /// solc: structs/struct_memory_to_storage.sol — a memory struct assigned into storage.
    function memoryStructToStorage() public {
        Inner memory m;
        m.a = 1;
        m.b = 2;
        m.c = 3;
        inner = m;
        assert(inner.a == 1);
        assert(inner.b == 2);
        assert(inner.c == 3);
    }

    /// solc: structs/copy_from_storage.sol — the storage-to-memory copy is deep: a later write
    /// to the storage source does not reach the memory copy.
    function storageToMemoryCopyIsDeep() public {
        x.s.a = 17;
        Inner memory m = x.s;
        x.s.a = 18;
        assert(m.a == 17);
    }

    /// solc: structs/copy_to_mapping.sol — the memory-to-storage copy is deep in the other
    /// direction too.
    function memoryToStorageCopyIsDeep() public {
        Inner memory m;
        m.a = 50;
        inner = m;
        m.a = 51;
        assert(inner.a == 50);
    }

    /// solc: structs/memory_structs_nested.sol — a memory struct member is a reference, so two
    /// locals bound to it alias each other.
    function memoryAliasIsNotACopy() public pure {
        Outer memory o;
        Inner memory ref = o.s;
        ref.a = 100;
        assert(o.s.a == 100);
    }

    /// solc: structs/memory_structs_nested.sol — an array held by a memory struct is indexable
    /// once it has been allocated.
    function memoryArrayInStruct() public pure {
        Basket memory b;
        uint[] memory xs = new uint[](4);
        b.items = xs;
        b.items[1] = 33;
        assert(b.items[1] == 33);
    }

    /// solc: array/delete/memory_arrays_delete.sol — `delete x[i]` resets one memory element
    /// and leaves its neighbour alone.
    function deleteMemoryArrayElement() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 17;
        xs[2] = 18;
        delete xs[1];
        assert(xs[1] == 0);
        assert(xs[2] == 18);
    }

    /// solc: array/copying/array_copy_storage_to_memory.sol — a whole storage array copied
    /// into memory.
    /// @custom:key box
    function storageArrayCopiedIntoMemory() public {
        require(prims.length == 2);
        prims[0] = 3;
        prims[1] = 4;
        uint[] memory m = prims;
        assert(m[0] == 3);
        assert(m[1] == 4);
    }
}
