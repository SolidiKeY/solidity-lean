// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
import "MixedHeap.sol";

contract AggregateWriteback is MixedHeap {
    function allFields() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        b.flag = false; b.number = type(uint256).max; b.left = bytes(t); b.right = bytes(t);
        observe(a,t,f,b,d,u);
    }
    function reverseFields() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        b.right = bytes(t); b.left = bytes(t); b.number = type(uint256).max; b.flag = false;
        observe(a,t,f,b,d,u);
    }
    function updateSharedChild() external pure returns (bytes memory) {
        (bytes memory a, string memory t, uint[2] memory f, Box memory b, bytes[] memory d, bytes memory u) = objects(reserve());
        b.flag = false; b.number = type(uint256).max; b.left = bytes(t); b.right = bytes(t);
        b.left[0] = 0xab;
        observe(a,t,f,b,d,u);
    }
    function revertFields() external pure {
        (, string memory t,, Box memory b,,) = objects(reserve());
        b.flag = false; b.number = type(uint256).max; b.left = bytes(t); b.right = bytes(t);
        b.left[0] = 0xab;
        revert();
    }
}
