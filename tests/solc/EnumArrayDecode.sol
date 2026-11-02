// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.4;

// `abi.decode` of nested enums through the solc import (lane FU2-D): still
// refused, "ABI decoding of enum values requires nominal cardinality
// checks". `sol{}` decodes an array of enums at the member count
// (`abiReadGen`, `EnumArrayDecode` in Examples/Tactics/AbiFeatures.lean;
// EVM vectors in tests/abi-0.8.38/EnumArrays.vectors.json), but the import
// declares enum-array locals at their `uint8` carrier, and `sol{}` reads a
// struct's enum member as a `uint`, its enum lost.
contract EnumArrayDecode {
    enum E { A, B, C }
    struct S { E e; uint x; }

    /// @custom:key box
    function dynamicArray(bytes memory b) public pure {
        E[] memory es = abi.decode(b, (E[]));
        assert(es.length == es.length);
    }

    /// @custom:key box
    function fixedArray(bytes memory b) public pure {
        E[2] memory es = abi.decode(b, (E[2]));
        assert(uint(es[0]) < 3);
    }

    /// @custom:key box
    function structMember(bytes memory b) public pure {
        S memory s = abi.decode(b, (S));
        assert(uint(s.e) < 3);
    }
}
