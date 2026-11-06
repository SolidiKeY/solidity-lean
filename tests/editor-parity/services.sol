// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;
contract Services {
  function helper(uint a, uint b) public pure returns(uint) {return a+b;}
  function caller() public view returns(uint) {return this.helper(1,2);}
}
