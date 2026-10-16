// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract Overloads {
    function pick(uint x) internal pure returns (uint) { return x + 1; }
    function pick(bool x) internal pure returns (uint) { return x ? 7 : 3; }
    // The pinned compiler gives the first pick declaration ID 13.
    function pick__solc13(uint x) internal pure returns (uint) { return x + 5; }
    /// @custom:key box
    function choosesByDeclaration() public pure {
        assert(pick(uint(4)) == 5);
        assert(pick(true) == 7);
        assert(pick(false) == 3);
        assert(pick__solc13(4) == 9);
    }
    /// @custom:key box
    function falsePost() public pure { assert(pick(true) == 3); }
    /// @custom:key box
    function check(uint x) public pure { assert(pick(x) == x + 1); }
    /// @custom:key box
    function check(bool x) public pure { assert(pick(x) == (x ? 7 : 3)); }
    enum Flavor { Red, Blue }
    type Coin is uint;
    function typedPick(uint x) internal pure returns (uint) { return x; }
    function typedPick(Flavor x) internal pure returns (uint) { return uint(x) + 10; }
    function typedPick(Coin x) internal pure returns (uint) { return Coin.unwrap(x) + 20; }
    /// @custom:key box
    function selectsDistinctSourceTypes() public pure {
        assert(typedPick(uint(1)) == 1);
        assert(typedPick(Flavor.Blue) == 11);
        assert(typedPick(Coin.wrap(1)) == 21);
    }
    enum uint256Flavor { Red, Blue }
    enum uintFlavor { Red, Blue }
    function namedType(uint256Flavor) internal pure returns (uint) { return 1; }
    function namedType(uintFlavor) internal pure returns (uint) { return 2; }
}
