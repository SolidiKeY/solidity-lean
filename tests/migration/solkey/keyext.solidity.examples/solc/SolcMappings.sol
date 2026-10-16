// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of the mapping tests of the solc compiler test suite:
/// `semanticTests/structs/struct_storage_to_mapping.sol`, `structs/copy_from_mapping.sol`,
/// `structs/copy_substructures_to_mapping.sol` and
/// `array/copying/array_elements_to_mapping.sol`.
///
/// Upstream's structs carry `bytes` and `uint16[]` members, which the calculus has no types
/// for; the ports keep the mapping-copy shape and use `uint` members instead.
contract SolcMappings {
    struct S { uint a; }
    struct Sub { uint x; uint y; }
    struct WithSub { uint a; Sub sub; }
    struct Ledger { uint nonce; mapping(uint => uint) balances; }

    S s;
    WithSub withSub;
    mapping(uint => S) m;
    mapping(uint => WithSub) withSubMap;
    mapping(uint => uint) balances;
    mapping(uint => uint[]) arrayMap;
    uint[][] rows;
    Ledger ledger;

    /// solc: structs/struct_storage_to_mapping.sol — `m[1] = s;` copies the storage struct into
    /// the mapping entry.
    function structStorageToMappingEntry() public {
        s.a = 12;
        m[1] = s;
        assert(m[1].a == 12);
    }

    /// solc: structs/copy_from_mapping.sol — the copy out of a mapping entry into a state
    /// struct.
    function mappingEntryToStorageStruct() public {
        m[1].a = 7;
        s = m[1];
        assert(s.a == 7);
    }

    /// solc: structs/struct_storage_to_mapping.sol — the copy is deep: writing the source
    /// afterwards does not reach the entry.
    function mappingEntryCopyIsDeep() public {
        s.a = 12;
        m[1] = s;
        s.a = 13;
        assert(m[1].a == 12);
    }

    /// solc: structs/copy_substructures_to_mapping.sol — a struct with a nested struct copied
    /// into a mapping entry keeps both levels.
    function copySubstructureIntoMapping() public {
        withSub.a = 1;
        withSub.sub.x = 2;
        withSub.sub.y = 3;
        withSubMap[5] = withSub;
        assert(withSubMap[5].a == 1);
        assert(withSubMap[5].sub.x == 2);
        assert(withSubMap[5].sub.y == 3);
    }

    /// solc: structs/copy_substructures_from_mapping.sol — and back out again.
    function copySubstructureFromMapping() public {
        withSubMap[5].a = 1;
        withSubMap[5].sub.x = 2;
        withSub = withSubMap[5];
        assert(withSub.a == 1);
        assert(withSub.sub.x == 2);
    }

    /// solc: structs/struct_delete_struct_in_mapping.sol — distinct keys are independent.
    function mappingKeysAreIndependent() public {
        balances[1] = 10;
        balances[2] = 20;
        delete balances[1];
        assert(balances[1] == 0);
        assert(balances[2] == 20);
    }

    /// No upstream twin — the Solidity language rule that `delete` on a struct resets its
    /// value members but leaves its mapping members alone (solc has no semantic test for it
    /// because the result is not observable through its return-value harness). This is what
    /// SolKey's lazy `delNode` marker implements.
    function deleteStructKeepsMappingMember() public {
        ledger.nonce = 5;
        ledger.balances[1] = 10;
        delete ledger;
        assert(ledger.nonce == 0);
        assert(ledger.balances[1] == 10);
    }

    /// solc: array/copying/array_elements_to_mapping.sol — the upstream `m[0] = s[0];` copies a
    /// whole array into a mapping entry.
    /// @custom:key box
    function arrayElementsToMapping() public {
        require(rows.length == 1);
        require(rows[0].length == 2);
        rows[0][0] = 10;
        rows[0][1] = 11;
        uint[] storage row = rows[0];
        arrayMap[0] = row;
        assert(arrayMap[0][0] == 10);
        assert(arrayMap[0][1] == 11);
    }

    /// solc: array/copying/array_elements_to_mapping.sol — the same copy performed element by
    /// element through the mapping entry's own array.
    /// @custom:key box
    function arrayElementsToMappingElementwise() public {
        require(rows.length == 1);
        require(rows[0].length == 2);
        require(arrayMap[0].length == 0);
        rows[0][0] = 10;
        rows[0][1] = 11;
        // a `push` argument that reads storage has to be bound first
        uint v0 = rows[0][0];
        uint v1 = rows[0][1];
        arrayMap[0].push(v0);
        arrayMap[0].push(v1);
        assert(arrayMap[0].length == 2);
        assert(arrayMap[0][0] == 10);
        assert(arrayMap[0][1] == 11);
    }
}
