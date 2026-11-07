// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
interface IA {}
interface IB is IA {}
contract C is IB {}
