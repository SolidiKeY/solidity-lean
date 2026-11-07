// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
interface IA {}
interface IB is IA {}
interface IC is IA {}
interface ID is IB, IC {}
