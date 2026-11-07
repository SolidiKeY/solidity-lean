// SPDX-License-Identifier: MIT
pragma solidity ^0.8.38;
contract C{function g() external pure returns(uint){return 1;}function f() public{try this.g(){}catch(bytes memory raw){assembly("memory-safe"){revert(add(raw,32),mload(raw))}}}}
