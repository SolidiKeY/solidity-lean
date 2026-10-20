// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
// A base's private variable and a derived one of the same name are two
// storage roots: the base's is renamed by its declaration (`x_PrivateRoot`).
contract PrivateRoot {
    uint private x;
    function setRoot() internal { x = 1; }
    function rootX() internal view returns (uint) { return x; }
}
contract NameShadow is PrivateRoot {
    uint private x;
    function f() public { x = 2; setRoot(); assert(x == 2 && rootX() == 1); }
    function falseShared() public { x = 2; setRoot(); assert(x == 1); }
}
/// @custom:key invariant x >= 0
contract NameGap is PrivateRoot { uint private x; function f() public pure { assert(true); } }
