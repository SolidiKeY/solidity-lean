// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.34;
// Guards H90 dynamic bytes/string local admission against marker erasure.
contract DynamicBytesBoundary {
 function bytesDefault() external pure { bytes memory b; }
 function stringDefault() external pure { string memory s; }
 function bytesAlias() external pure { bytes memory a; bytes memory b = a; }
 function stringAlias() external pure { string memory a; string memory b = a; }
 function bytesAllocate() external pure { bytes memory b = new bytes(2); }
 function stringLiteral() external pure { string memory s = "hi"; }
 function bytesParameter(bytes memory b) public pure { }
 function stringParameter(string memory s) public pure { }
}
contract DynamicBytesState { bytes b; function untouched() external pure { } }
contract DynamicStringState { string s; function untouched() external pure { } }
