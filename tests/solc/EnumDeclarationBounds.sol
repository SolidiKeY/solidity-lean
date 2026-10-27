pragma solidity ^0.8.0;

library ForeignEnumBounds {
    enum E { A, B }
}

contract EnumDeclarationBounds {
    enum E { A, B, C }

    function foreignRead(uint choice) public pure returns (uint) {
        return uint(ForeignEnumBounds.E(choice));
    }
    function localAccepts() public pure {
        E value = E(2);
        assert(value == E.C);
    }
}
