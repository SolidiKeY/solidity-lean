// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
import "MixedHeap.sol";

contract WordWriteback is MixedHeap {
    function pointerThenScalar() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        b.right = bytes(t); f[1] = 42;
        observe(a,t,f,b,d,u);
    }
    function scalarThenPointer() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        f[1] = 42; b.right = bytes(t);
        observe(a,t,f,b,d,u);
    }
    function maximumUint() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        f[1] = type(uint256).max;
        observe(a,t,f,b,d,u);
    }
    function revertBoth() external pure {
        (, string memory t, uint[2] memory f, Box memory b,,) = objects(reserve());
        f[1] = 42; b.right = bytes(t);
        revert();
    }
}
