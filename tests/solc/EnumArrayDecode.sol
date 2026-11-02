// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.4;

// `abi.decode` of nested enums through the solc import (lane FU2-D): the
// import prints each component as `solcEnumBelow(T, "k", n, …)`, `T` at its
// carriers and each enum position `k` checked below its member count `n`
// (`abiReadGen`); the EVM vectors are tests/abi-0.8.38/EnumArrays.vectors.json,
// replayed by tests/upstream/EnumArrays.lean.
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
