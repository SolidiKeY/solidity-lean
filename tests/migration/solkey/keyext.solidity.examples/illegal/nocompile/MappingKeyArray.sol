// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Expected '=>' but got '['
///
/// A non-elementary key is rejected before type checking: the grammar admits no `[` here.
contract MappingKeyArray {
    mapping(uint[] => uint) byArray;
}
