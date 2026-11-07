// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
contract ScalarMemoryAlias {
    function bytesAliases() external pure returns (uint[12] memory out) {
        bytes3[] memory a = new bytes3[](2); bytes3[] memory b = a;
        a[0] = hex"112233"; a[1] = hex"aa00ff"; b[0] = hex"ff00aa";
        assembly ("memory-safe") {
            mstore(out, mload(a)) mstore(add(out,32), mload(b))
            mstore(add(out,64), mload(add(a,32))) mstore(add(out,96), mload(add(b,32)))
            mstore(add(out,128), mload(add(a,64))) mstore(add(out,160), mload(add(b,64)))
            mstore(add(out,256), eq(a,b)) mstore(add(out,288), mload(0x60))
        }
        out[6] = uint8(a[0][0]); out[7] = uint8(b[0][0]); out[10] = uint8(a[1][0]); out[11] = uint8(b[1][2]);
    }
    function signedAliases() external pure returns (uint[12] memory out) {
        int8[4] memory a; int8[4] memory b = a;
        a[0] = -128; a[1] = -1; a[2] = 0; a[3] = 127; b[1] = -128;
        assembly ("memory-safe") {
            mstore(out, mload(a)) mstore(add(out,32), mload(b))
            mstore(add(out,64), mload(add(a,32))) mstore(add(out,96), mload(add(b,32)))
            mstore(add(out,128), mload(add(a,64))) mstore(add(out,160), mload(add(b,96)))
            mstore(add(out,256), eq(a,b)) mstore(add(out,288), mload(0x60))
        }
        out[6] = uint256(int256(a[1])); out[7] = uint256(int256(b[1])); out[10] = uint256(int256(a[3])); out[11] = uint256(int256(b[0]));
    }
    function addressAliases() external pure returns (uint[12] memory out) {
        address[] memory a = new address[](2); address[] memory b = a;
        a[0] = address(1); a[1] = address(0x1234); b[0] = address(type(uint160).max);
        assembly ("memory-safe") {
            mstore(out, mload(a)) mstore(add(out,32), mload(b))
            mstore(add(out,64), mload(add(a,32))) mstore(add(out,96), mload(add(b,32)))
            mstore(add(out,128), mload(add(a,64))) mstore(add(out,160), mload(add(b,64)))
            mstore(add(out,256), eq(a,b)) mstore(add(out,288), mload(0x60))
        }
        out[6] = uint160(a[0]); out[7] = uint160(b[0]); out[10] = uint160(a[1]); out[11] = uint160(b[1]);
    }
    function regrowAliases() external pure returns (uint[12] memory out) {
        bytes3[] memory a = new bytes3[](2); bytes3[] memory b = a;
        a[0] = hex"112233"; a[1] = hex"aa00ff";
        assembly ("memory-safe") {
            mstore(b,0) mstore(out,mload(a)) mstore(add(out,32),mload(b))
            mstore(add(out,64),mload(add(a,32))) mstore(add(out,96),mload(add(b,32)))
            mstore(a,2) mstore(add(out,128),mload(a)) mstore(add(out,160),mload(b))
        }
        b[0] = hex"ff00aa";
        out[6] = uint8(a[0][0]); out[7] = uint8(b[0][0]);
        assembly ("memory-safe") {
            mstore(add(out,256),eq(a,b)) mstore(add(out,288),mload(0x60))
            mstore(add(out,320),mload(add(a,32))) mstore(add(out,352),mload(add(b,64)))
        }
    }
    function badAliasedIndex() external pure returns (bytes3) {
        bytes3[] memory a = new bytes3[](2); bytes3[] memory b = a;
        a[0] = hex"112233";
        assembly ("memory-safe") { mstore(a,0) }
        return b[0];
    }
    function revertAliases() external pure {
        bytes3[] memory a = new bytes3[](2); bytes3[] memory b = a;
        b[0] = hex"ff00aa"; require(a[0] == hex"ff00aa"); revert();
    }
}
