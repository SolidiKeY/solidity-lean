// SPDX-License-Identifier: MIT
pragma solidity ^0.8.38;
contract C{function g() external pure returns(uint){return 1;}function f() public{try this.g()returns(uint v){v;}catch Error(string memory reason){reason;}catch Panic(uint code){code;}catch(bytes memory raw){raw;}}}
