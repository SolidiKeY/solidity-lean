// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
// keccak256, the ABI and string-keyed mappings (docs/semantic-gaps.md,
// "Hashing and the ABI"): keccak256 Keccak-256 of the bytes (an atom to the
// closers, evaluated on literal bytes),
// abi.encode/encodePacked fresh memory bytes of solc's layout, abi.decode its
// inverse, a mapping(string => V) keyed by the hash.

contract Hashing {
    mapping(string => uint) ids;

    // one string hashed twice: the hash is a function; under the diamond
    // the closer reads the bytes off the memory and evaluates the hash
    function equalStringsHashEqual() public pure {
        string memory s = "ab";
        assert(keccak256(bytes(s)) == keccak256(bytes(s)));
    }
    function literalHash() public pure {
        bytes memory b = "abc";
        assert(keccak256(b) == bytes32(0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45));
    }
    function twoAllocationsHashEqual() public pure {
        bytes memory b = "ab";
        bytes memory c = "ab";
        assert(keccak256(b) == keccak256(c));
    }
    function hashParameter(bytes memory b) public pure {
        assert(keccak256(b) == keccak256(b));
    }
    function encodeLayout() public pure {
        bytes memory e = abi.encode(uint16(258), true, uint8(0x12));
        assert(e.length == 96 && e[30] == 0x01 && e[31] == 0x02 && e[63] == 0x01 &&
            e[95] == 0x12 && e[0] == 0);
    }
    // a symbolic address written byte by byte, read back (`hornerU?`,
    // `modShrModU?`, `Calculus/Closer.lean`)
    function packedAddressBytes(address a) public pure {
        bytes memory e = abi.encodePacked(a);
        assert(uint8(e[19]) == uint8(uint160(a)));
    }
    // eight bytes reassembled by Horner's rule (an address's twenty are past
    // the closer's bounds, `Seq.closeSize`)
    function packedWordReassembled(uint64 x) public pure {
        bytes memory e = abi.encodePacked(x);
        uint r = uint8(e[0]);
        r = r * 256 + uint8(e[1]);
        r = r * 256 + uint8(e[2]);
        r = r * 256 + uint8(e[3]);
        r = r * 256 + uint8(e[4]);
        r = r * 256 + uint8(e[5]);
        r = r * 256 + uint8(e[6]);
        r = r * 256 + uint8(e[7]);
        assert(r == x);
    }
    function encodePacked() public pure {
        bytes memory e = abi.encodePacked(uint16(258), true, bytes2("ab"));
        assert(e.length == 5 && e[0] == 0x01 && e[1] == 0x02 && e[2] == 0x01 && e[3] == "a");
    }
    function decodeRoundtrip() public pure {
        bytes memory e = abi.encode(true);
        bool c = abi.decode(e, (bool));
        assert(c);
    }
    function stringKey(string memory k) public {
        ids[k] = 7;
        assert(ids[k] == 7);
    }
    function concatLengths() public pure {
        string memory s = string.concat("ab", "cde");
        bytes memory t = bytes.concat("x", "yz");
        assert(bytes(s).length == 5 && t.length == 3);
    }
    // a selector before the arguments: a literal signature's folded as solc
    // folds it (`f(uint256)` is 0xb3de648b)
    function encodeWithSignature() public pure {
        bytes memory e = abi.encodeWithSignature("f(uint256)", 1);
        assert(e.length == 36 && e[0] == 0xb3 && e[3] == 0x8b && e[35] == 0x01);
    }
    function encodeWithSelector() public pure {
        bytes memory e = abi.encodeWithSelector(bytes4(0x01020304), true);
        assert(e.length == 36 && e[1] == 0x02 && e[35] == 0x01);
    }
    function f(uint x) public pure returns (uint) { return x; }
    function encodeCall() public view {
        bytes memory e = abi.encodeCall(this.f, (2));
        assert(e.length == 36 && e[0] == 0xb3 && e[35] == 0x02);
    }
    // an enum packs at one byte (an address at 20: `Codec2.packedWidths` of
    // `Examples/Tactics/Hashing.lean`)
    enum Color { Red, Green }
    function packedEnum() public pure {
        bytes memory e = abi.encodePacked(Color.Green, uint8(7));
        assert(e.length == 2 && e[0] == 0x01 && e[1] == 0x07);
    }
    // a struct of values: its members' words inline in the head (arrays and a
    // decoded byte string are read element by element: run in
    // `Examples/Tactics/Hashing.lean`, `Codec2`)
    struct Pt { uint x; bool y; }
    function encodeStruct() public pure {
        Pt memory p = Pt(3, true);
        bytes memory e = abi.encode(p);
        assert(e.length == 64 && e[31] == 0x03 && e[63] == 0x01);
    }
    // `sha256` and `ripemd160`, the precompiles: SHA-256 and RIPEMD-160 of
    // the bytes (`Hashes.lean`), atoms to the closers as `keccak256` is
    function sha256Parameter(bytes memory b) public pure {
        assert(sha256(b) == sha256(b));
    }
    function ripemd160Parameter(bytes memory b) public pure {
        assert(ripemd160(b) == ripemd160(b));
    }
    // of a byte string built here, under the diamond: evaluated (`keccakAt`)
    function sha256Literal() public pure {
        bytes memory b = "abc";
        assert(sha256(b) == bytes32(0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad));
    }
    function ripemd160Literal() public pure {
        bytes memory b = "abc";
        assert(uint160(ripemd160(b)) == 814647003348588794217809277549781461204094028796);
    }
    // `ecrecover`: the precompile's 128 bytes, an address, uninterpreted where
    // the signature is well formed (`ecrecoverBytes`); run in
    // `Examples/Tactics/Hashing.lean`
    /// @custom:key box
    function recoverSigner(bytes32 h, uint8 v, bytes32 r, bytes32 s) public pure returns (address) {
        return ecrecover(h, v, r, s);
    }
    // `abi.decode` of a struct of values and of a `T[k]`: their words in the
    // head, each read back (a word out of range reverting); of a `T[]`, its
    // offset, length and words, read by a loop (run in
    // `Examples/Tactics/Hashing.lean`, `Codec2`)
    /// @custom:key box
    function decodeStruct(bytes memory d) public pure returns (uint) {
        Pt memory q = abi.decode(d, (Pt));
        return q.x;
    }
    /// @custom:key box
    function decodeFixed(bytes memory d) public pure returns (uint) {
        uint8[2] memory zs = abi.decode(d, (uint8[2]));
        return zs[1];
    }
    /// @custom:key box
    function decodeTuple(bytes memory d) public pure returns (uint) {
        (uint a, Pt memory q) = abi.decode(d, (uint, Pt));
        return a + q.x;
    }
}
