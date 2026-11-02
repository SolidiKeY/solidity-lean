// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

// Enums nested in ABI types (lane FU2-D): `abi.decode` of an enum array, an
// enum array or a struct with an enum member at the external entry, and a
// public enum getter.  `scripts/enum-abi-probe.mjs` runs the vectors on the
// EVM; `Examples/Tactics/AbiFeatures.lean` (`EnumArrayDecode`) replays the
// `abi.decode` ones.
contract EnumArrays {
    enum E { A, B, C }
    struct S { E e; uint x; }

    E public stored;

    function decodeArr(uint a, uint b) public pure returns (uint r) {
        uint[] memory xs = new uint[](2);
        xs[0] = a;
        xs[1] = b;
        E[] memory es = abi.decode(abi.encode(xs), (E[]));
        r = uint(es[0]) * 10 + uint(es[1]);
    }

    function decodeFixed(uint a, uint b) public pure returns (uint r) {
        E[2] memory es = abi.decode(abi.encode(a, b), (E[2]));
        r = uint(es[0]) * 10 + uint(es[1]);
    }

    function entryArr(E[] memory es) public pure returns (uint) {
        return es.length * 100 + uint(es[0]);
    }

    function entryStruct(S memory s) public pure returns (uint) {
        return uint(s.e) * 1000 + s.x;
    }

    function setStored(uint v) public {
        stored = E(v);
    }
}
