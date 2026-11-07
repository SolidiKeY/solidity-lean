// Guards H90 existing environment-member routing and unsupported siblings.
pragma solidity ^0.8.34;
contract EnvironmentMembers {
 function valueSelf() external payable { assert(msg.value == msg.value); }
 function valueCopy() external payable { uint256 v = msg.value; assert(v == msg.value); }
 function nonnegativeValue() external payable { assert(msg.value >= 0); }
 function wrongValue() external payable { assert(msg.value != msg.value); }
 function timeCopy() external view { uint256 t = block.timestamp; assert(t == block.timestamp); }
 function wrongTime() external view { uint256 t = block.timestamp; assert(t != block.timestamp); }
 function siblingBlock() external view { assert(block.number == block.number); }
 function siblingTx() external view { assert(tx.origin == tx.origin); }
}
