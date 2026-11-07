// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
contract RetainedMemberArrays {
    function initial() external pure returns (bytes memory) { run(0); }
    function shrinkZero() external pure returns (bytes memory) { run(1); }
    function regrowBoth() external pure returns (bytes memory) { run(2); }
    function partialRegrow() external pure returns (bytes memory) { run(3); }
    function reverseRegrow() external pure returns (bytes memory) { run(4); }
    function sharedAfterRegrow() external pure returns (bytes memory) { run(5); }
    function revertRegrow() external pure { run(6); }
    function run(uint mode) internal pure {
        uint start;
        assembly ("memory-safe") { start := mload(0x40) mstore(0x40, add(start, 1792)) }
        bool[3] memory flags; bytes[2] memory refs;
        bool[] memory dynamicFlags; bytes[] memory dynamicRefs;
        bytes memory a; string memory text; bytes memory other;
        assembly ("memory-safe") {
            flags := start refs := add(start, 256) dynamicFlags := add(start, 512) dynamicRefs := add(start, 768)
            a := add(start, 1024) text := add(start, 1280) other := add(start, 1536)
            for { let p := start } lt(p, add(start, 1792)) { p := add(p, 32) } {
                mstore(p, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            }
            mstore(flags, 0) mstore(add(flags, 32), 1) mstore(add(flags, 64), 0)
            mstore(refs, a) mstore(add(refs, 32), a)
            mstore(dynamicFlags, 3) mstore(add(dynamicFlags, 32), 0) mstore(add(dynamicFlags, 64), 1) mstore(add(dynamicFlags, 96), 0)
            mstore(dynamicRefs, 2) mstore(add(dynamicRefs, 32), a) mstore(add(dynamicRefs, 64), a)
            mstore(a, 3) mstore(add(a, 32), 0x112233a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(text, 2) mstore(add(text, 32), 0xff61a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(other, 3) mstore(add(other, 32), 0xeeddcca5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
        }
        if (mode == 4) {
            assembly ("memory-safe") { mstore(dynamicRefs, 0) mstore(dynamicRefs, 2) mstore(dynamicFlags, 0) mstore(dynamicFlags, 3) }
        } else if (mode != 0) {
            assembly ("memory-safe") { mstore(dynamicFlags, 0) mstore(dynamicRefs, 0) }
            if (mode >= 2) {
                assembly ("memory-safe") { mstore(dynamicFlags, 3) mstore(dynamicRefs, 2) }
                if (mode == 3) { assembly ("memory-safe") { mstore(dynamicFlags, 1) mstore(dynamicRefs, 1) } }
            }
        }
        if (mode == 5) { dynamicRefs[0] = bytes(text); dynamicRefs[1] = bytes(text); dynamicRefs[0][0] = 0xab; }
        if (mode == 6) { dynamicRefs[0] = bytes(text); dynamicRefs[0][0] = 0xab; revert(); }
        uint oldFree;
        assembly ("memory-safe") { oldFree := mload(0x40) }
        uint[56] memory out;
        assembly ("memory-safe") {
            mstore(add(out, 0), mload(flags))
            mstore(add(out, 32), mload(add(flags, 32)))
            mstore(add(out, 64), mload(add(flags, 64)))
            mstore(add(out, 96), mload(refs))
            mstore(add(out, 128), mload(add(refs, 32)))
            mstore(add(out, 160), mload(dynamicFlags))
            mstore(add(out, 192), mload(add(dynamicFlags, 32)))
            mstore(add(out, 224), mload(add(dynamicFlags, 64)))
            mstore(add(out, 256), mload(add(dynamicFlags, 96)))
            mstore(add(out, 288), mload(dynamicRefs))
            mstore(add(out, 320), mload(add(dynamicRefs, 32)))
            mstore(add(out, 352), mload(add(dynamicRefs, 64)))
            mstore(add(out, 384), mload(a))
            mstore(add(out, 416), mload(add(a, 32)))
            mstore(add(out, 448), mload(text))
            mstore(add(out, 480), mload(add(text, 32)))
            mstore(add(out, 512), mload(other))
            mstore(add(out, 544), mload(add(other, 32)))
            mstore(add(out, 608), mload(0x60))
            mstore(add(out, 1152), mload(add(flags, 96)))
            mstore(add(out, 1184), mload(add(refs, 64)))
            mstore(add(out, 1216), mload(add(dynamicFlags, 128)))
            mstore(add(out, 1248), mload(add(dynamicRefs, 96)))
            mstore(add(out, 1280), mload(add(a, 64)))
            mstore(add(out, 1312), mload(add(text, 64)))
            mstore(add(out, 1344), mload(add(other, 64)))
        }
        out[18] = oldFree;
        out[20] = flags[0] ? 1 : 0;
        out[21] = flags[1] ? 1 : 0;
        out[22] = flags[2] ? 1 : 0;
        out[23] = dynamicFlags.length > 0 ? (dynamicFlags[0] ? 1 : 0) : 0;
        out[24] = dynamicFlags.length > 1 ? (dynamicFlags[1] ? 1 : 0) : 0;
        out[25] = dynamicFlags.length > 2 ? (dynamicFlags[2] ? 1 : 0) : 0;
        out[26] = refs[0].length;
        out[27] = refs[1].length;
        out[28] = uint8(refs[0][0]);
        out[29] = uint8(refs[1][0]);
        out[30] = dynamicRefs.length > 0 ? dynamicRefs[0].length : 0;
        out[31] = dynamicRefs.length > 1 ? dynamicRefs[1].length : 0;
        out[32] = dynamicRefs.length > 0 ? uint8(dynamicRefs[0][0]) : 0;
        out[33] = dynamicRefs.length > 1 ? uint8(dynamicRefs[1][0]) : 0;
        assembly ("memory-safe") {
            mstore(add(out, 1088), eq(mload(refs), mload(add(refs, 32))))
            mstore(add(out, 1120), eq(mload(add(dynamicRefs, 32)), mload(add(dynamicRefs, 64))))
            mstore(add(out, 1376), mload(refs)) mstore(add(out, 1408), mload(add(refs, 32)))
            mstore(add(out, 1440), mload(add(dynamicRefs, 32))) mstore(add(out, 1472), mload(add(dynamicRefs, 64)))
        }
        out[47] = dynamicFlags.length; out[48] = dynamicRefs.length;
        out[49] = uint8(a[0]); out[50] = uint8(bytes(text)[0]); out[51] = uint8(other[0]);
        out[52] = uint8(a[2]); out[53] = uint8(bytes(text)[1]); out[54] = uint8(other[2]); out[55] = 0;
        assembly ("memory-safe") {
            let result := mload(0x40)
            mstore(result, 32) mstore(add(result, 32), 1792)
            mcopy(add(result, 64), out, 1792)
            return(result, 1856)
        }
    }
}
