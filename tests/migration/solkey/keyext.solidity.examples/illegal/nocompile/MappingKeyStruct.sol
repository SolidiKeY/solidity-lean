// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// solc: Only elementary types, user defined value types, contract types or enums are allowed as mapping keys.
///
/// A mapping key must be an elementary type; a struct is not one.
contract MappingKeyStruct {
    struct Person { uint age; }

    mapping(Person => uint) byPerson;
}
