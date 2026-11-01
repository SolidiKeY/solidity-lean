// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.38;
pragma abicoder v2;

// Probes of solc's generated ABI entry decoder (lane CF1). Vectors and the
// observed outcomes are in LazyEntry.vectors.json; they are replayed in
// legacy/viaIR with the optimizer off and on by scripts/abi-entry-probe.mjs.

/// Calldata references: only the entry checks run before the body.
contract CalldataNested {
    function outerLength(uint256[][] calldata x) external pure returns (uint256) { return x.length; }
    function innerLength(uint256[][] calldata x, uint256 i) external pure returns (uint256) { return x[i].length; }
    function element(uint256[][] calldata x, uint256 i, uint256 j) external pure returns (uint256) { return x[i][j]; }
    function narrow(uint8[] calldata x) external pure returns (uint256) { return x.length; }
    function narrowAt(uint8[] calldata x, uint256 i) external pure returns (uint8) { return x[i]; }
    function bytesLength(bytes calldata b) external pure returns (uint256) { return b.length; }
    function bytesArrayLength(bytes[] calldata b) external pure returns (uint256) { return b.length; }
    function bytesAt(bytes[] calldata b, uint256 i) external pure returns (uint256) { return b[i].length; }
    function copy(uint256[][] calldata x) external pure returns (uint256) { uint256[][] memory m = x; return m.length; }
}

/// Memory references: the whole value is decoded and validated at entry.
contract MemoryNested {
    function outerLength(uint256[][] memory x) public pure returns (uint256) { return x.length; }
    function narrow(uint8[] memory x) public pure returns (uint256) { return x.length; }
    function bytesLength(bytes memory b) public pure returns (uint256) { return b.length; }
    function bytesArrayLength(bytes[] memory b) public pure returns (uint256) { return b.length; }
    function stringLength(string memory s) public pure returns (uint256) { return bytes(s).length; }
    function two(bytes memory a, uint8 b) public pure returns (uint256) { return a.length + b; }
}

/// Calldata structs: the head must fit; dynamic members are lazy.
contract CalldataStruct {
    struct S { uint256 a; uint256[] b; }
    function a(S calldata s) external pure returns (uint256) { return s.a; }
    function bLength(S calldata s) external pure returns (uint256) { return s.b.length; }
    function m(S memory s) public pure returns (uint256) { return s.a; }
}

/// Static calldata arrays: the whole static block is bounds-checked at entry.
contract CalldataStatic {
    function first(uint256[2][2] calldata x) external pure returns (uint256) { return x[0][0]; }
    function narrowFirst(uint8[2] calldata x) external pure returns (uint256) { return x.length; }
    function narrowAt(uint8[2] calldata x, uint256 i) external pure returns (uint8) { return x[i]; }
}

/// Enum parameters: validated against the declared cardinality at entry.
contract EnumEntry {
    enum E { A, B, C }
    function value(E e) external pure returns (uint8) { return uint8(e); }
    function withArray(E e, uint8[] calldata xs) external pure returns (uint256) { return uint8(e) + xs.length; }
    function memoryArray(E e, uint8[] memory xs) public pure returns (uint256) { return uint8(e) + xs.length; }
}
