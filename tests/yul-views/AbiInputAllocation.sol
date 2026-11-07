// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

// Finite memory-input evidence only. No ABI admission or compiler adequacy claim.
contract AbiInputAllocation {
    uint public marker = 4242;
    function snapshot(bytes memory packet, uint tag) internal pure returns (uint[10] memory out) {
        uint[] memory xs = abi.decode(packet, (uint[]));
        uint[] memory alias_ = xs;
        if (tag == 1 && xs.length != 0) alias_[0] = 99;
        out[0] = tag;
        out[1] = xs.length;
        if (xs.length > 0) out[2] = xs[0];
        if (xs.length > 1) out[3] = xs[1];
        if (xs.length > 2) out[4] = xs[2];
        assembly ("memory-safe") {
            mstore(add(out,160),mload(xs))
            if gt(mload(xs),0) { mstore(add(out,192),mload(add(xs,32))) }
            if gt(mload(xs),1) { mstore(add(out,224),mload(add(xs,64))) }
            if gt(mload(xs),2) { mstore(add(out,256),mload(add(xs,96))) }
            mstore(add(out,288),eq(xs,alias_))
        }
    }
    function inspect(bytes memory packet) external pure returns (uint[10] memory) { return snapshot(packet,0); }
    function mutated(bytes memory packet) external pure returns (uint[10] memory) { return snapshot(packet,1); }
    function at(bytes memory packet,uint i) external pure returns (uint) { uint[] memory xs=abi.decode(packet,(uint[])); return xs[i]; }
    function bools(bytes memory packet) external pure returns (bool) { bool[] memory xs=abi.decode(packet,(bool[])); return xs[0]; }
    function fail(bytes memory packet) external { marker=8888; snapshot(packet,0); revert("abi-array"); }
    function staticProbe(bytes memory packet) external view returns (bool,bytes memory) {
        return address(this).staticcall(abi.encodeCall(this.inspect,(packet)));
    }
}
