// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

contract MixedHeap {
    struct Box { bool flag; uint256 number; bytes left; bytes right; bytes[] children; }
    function reserve() internal pure returns (uint start) {
        assembly ("memory-safe") { start := mload(0x40) mstore(0x40, add(start, 1536)) }
    }
    function objects(uint start) internal pure returns (bytes memory a, string memory text, uint[2] memory fixedA,
        Box memory box, bytes[] memory dynamicA, bytes memory other) {
        assembly ("memory-safe") {
            a := start
            text := add(start, 256)
            fixedA := add(start, 512)
            box := add(start, 768)
            dynamicA := add(start, 1024)
            other := add(start, 1280)
            for { let at := start } lt(at, add(start, 1536)) { at := add(at, 32) } {
                mstore(at, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            }
            mstore(a, 3)
            mstore(add(a, 32), 0x112233a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(text, 2)
            mstore(add(text, 32), 0xff61a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(fixedA, 7)
            mstore(add(fixedA, 32), 9)
            mstore(box, 1)
            mstore(add(box, 32), 7)
            mstore(add(box, 64), a)
            mstore(add(box, 96), a)
            mstore(add(box, 128), dynamicA)
            mstore(dynamicA, 2)
            mstore(add(dynamicA, 32), a)
            mstore(add(dynamicA, 64), a)
            mstore(other, 3)
            mstore(add(other, 32), 0xeeddcca5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
        }
    }
    function observe(bytes memory a, string memory text, uint[2] memory fixedA, Box memory box,
        bytes[] memory dynamicA, bytes memory other) internal pure {
        uint oldFree;
        assembly ("memory-safe") { oldFree := mload(0x40) }
        uint[40] memory out;
        assembly ("memory-safe") {
            mstore(out, mload(a))
            mstore(add(out, 32), mload(add(a, 32)))
            mstore(add(out, 64), mload(text))
            mstore(add(out, 96), mload(add(text, 32)))
            mstore(add(out, 128), mload(fixedA))
            mstore(add(out, 160), mload(add(fixedA, 32)))
            mstore(add(out, 192), mload(box))
            mstore(add(out, 224), mload(add(box, 32)))
            mstore(add(out, 256), mload(add(box, 64)))
            mstore(add(out, 288), mload(add(box, 96)))
            mstore(add(out, 320), mload(add(box, 128)))
            mstore(add(out, 352), mload(dynamicA))
            mstore(add(out, 384), mload(add(dynamicA, 32)))
            mstore(add(out, 416), mload(add(dynamicA, 64)))
            mstore(add(out, 448), mload(other))
            mstore(add(out, 480), mload(add(other, 32)))
            mstore(add(out, 544), mload(0x60))
            mstore(add(out, 576), mload(add(a, 64)))
            mstore(add(out, 608), mload(add(text, 64)))
            mstore(add(out, 640), mload(add(fixedA, 64)))
            mstore(add(out, 672), mload(add(box, 160)))
            mstore(add(out, 704), mload(add(dynamicA, 96)))
            mstore(add(out, 736), mload(add(other, 64)))
            mstore(add(out, 1120), eq(mload(add(box, 64)), mload(add(box, 96))))
            mstore(add(out, 1152), eq(mload(add(dynamicA, 32)), mload(add(dynamicA, 64))))
            mstore(add(out, 1184), mload(add(box, 64)))
        }
        out[16] = oldFree;
        out[24] = box.flag ? 1 : 0;
        out[25] = box.number;
        out[26] = box.left.length;
        out[27] = box.right.length;
        out[28] = uint8(box.left[0]);
        out[29] = uint8(box.right[0]);
        out[30] = uint8(dynamicA[0][0]);
        out[31] = uint8(dynamicA[1][0]);
        out[32] = fixedA[0];
        out[33] = fixedA[1];
        out[34] = dynamicA.length;
        out[38] = uint8(a[2]);
        out[39] = uint8(bytes(text)[0]);
        assembly ("memory-safe") {
            let result := mload(0x40)
            mstore(result, 32)
            mstore(add(result, 32), 1280)
            mcopy(add(result, 64), out, 1280)
            return(result, 1344)
        }
    }
    function initial() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        observe(a,t,f,b,d,u);
    }
    function childWrite() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        a[0] = 0x99;
        observe(a,t,f,b,d,u);
    }
    function scalarWrite() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        f[1] = 42;
        observe(a,t,f,b,d,u);
    }
    function bothForward() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        a[0] = 0x99; f[1] = 42;
        observe(a,t,f,b,d,u);
    }
    function bothReverse() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        f[1] = 42; a[0] = 0x99;
        observe(a,t,f,b,d,u);
    }
    function retargetRight() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        b.right = bytes(t);
        observe(a,t,f,b,d,u);
    }
    function explicitRevert() external pure {
        (bytes memory a,,uint[2] memory f,,,) = objects(reserve());
        a[0] = 0x99; f[1] = 42;
        revert();
    }
}
