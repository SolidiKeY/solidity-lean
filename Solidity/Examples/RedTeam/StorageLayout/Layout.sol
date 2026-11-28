// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;
contract Packing { bool a; bool b; bool[2] flags; uint256 tail; }
contract Mixed { bool a; uint256 n; bool b; bool c; }
contract Shapes {
    struct Packed { bool a; bool b; }
    struct Wallet { uint256 owner; mapping(uint256 => uint256) stash; }
    Packed packed; uint256 afterPacked; Wallet wallet;
    uint256[3] fixedWords; uint256[] words; bool[] bits;
    mapping(uint256 => Wallet) wallets;
}
contract Base { bool baseFlag; }
contract Derived is Base { bool derivedFlag; uint256 tail; }
