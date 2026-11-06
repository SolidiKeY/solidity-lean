// SPDX-License-Identifier: GPL-3.0
// Lane FU2-C probes: a calldata element that fails only on access, read
// (index, length), encoded (abi.encode/abi.encodePacked) or copied to memory.
pragma solidity ^0.8.0;
pragma abicoder v2;
contract AccessEntry {
  function enc(uint256[][] calldata x) external pure returns (uint256) { return abi.encode(x).length; }
  function encAt(uint256[][] calldata x, uint256 i) external pure returns (uint256) { return abi.encode(x[i]).length; }
  function encIf(uint256[][] calldata x, uint256 i) external pure returns (uint256) { if (i == 0) return 7; return abi.encode(x).length; }
  function enc8(uint8[] calldata x) external pure returns (uint256) { return abi.encode(x).length; }
  function enc8n(uint8[][] calldata x) external pure returns (uint256) { return abi.encode(x).length; }
  function encB(bytes[] calldata x) external pure returns (uint256) { return abi.encode(x).length; }
  function enc3(uint256[][3] calldata x) external pure returns (uint256) { return abi.encode(x).length; }
  function encP(uint256[][] calldata x) external pure returns (uint256) { return abi.encodePacked(x[0]).length; }
  function cp(uint256[][] calldata x) external pure returns (uint256) { uint256[][] memory m = x; return m.length; }
  function cpAt(uint256[][] calldata x, uint256 i) external pure returns (uint256) { uint256[] memory m = x[i]; return m.length; }
  function encPw(uint8[] calldata x) external pure returns (uint256) { return abi.encodePacked(x).length; }
  function enc8nL(uint8[][] calldata x) external pure returns (uint256) { return abi.encode(x).length; }
  function encBL(bytes[] calldata x) external pure returns (uint256) { return abi.encode(x).length; }
  function order(uint8[] calldata x, uint256 k) external pure returns (uint256) { return x[0] + 1 / k; }
  function encReq(uint256[][] calldata x, uint256 i) external pure returns (uint256) { require(i != 0, "m"); return abi.encode(x).length; }
}
