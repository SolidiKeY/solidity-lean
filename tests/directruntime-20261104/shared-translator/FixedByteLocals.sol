// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.34;
/// Guards H90 fixed-byte local marker/bitwise/tuple regressions.
contract FixedByteLocals {
 function zero() public pure { bytes4 a; bytes4 b; assert(a == b); }
 function complement() public pure { bytes1 a; bytes1 b = ~a; assert(b != a); }
 function wideComplement() public pure { bytes32 a; bytes32 b = ~a; assert(b != a); }
 function tupleSwap() public pure { bytes4 a; bytes4 b = ~a; (a,b) = (b,a); assert(a != b); }
 function repeated() public pure { bytes4 a; bytes4 b = ~a; (a,a) = (b,a); assert(a == b); }
 function wrong() public pure { bytes1 a; bytes1 b = ~a; assert(a == b); }
 function length() public pure { bytes4 a; assert(a.length == 4); }
 function wrongLength() public pure { bytes4 a; assert(a.length == 5); }
 function widening() public pure { bytes1 a; a = ~a; bytes2 b = a; bytes1 z; assert(b[0] == a[0]); assert(b[1] == z); }
 function parameter(bytes4 a) public pure { assert(a == a); }
}
