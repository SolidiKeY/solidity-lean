pragma solidity ^0.8.0;

library FiniteEnum {
    enum E { A, B }
    struct LibraryPair { uint value; }
    function equals(E a, E b) internal pure returns (bool) { return a == b; }
}
interface FiniteAddress {}

contract FiniteTypeLowering {
    using FiniteEnum for FiniteEnum.E;
    enum E { A, B, C }
    struct Pair { uint value; }
    mapping(FiniteAddress => uint8) table;

    function enumIdentity() public pure {
        Pair memory value = Pair(7);
        assert(value.value == 7);
        assert(FiniteEnum.E.A.equals(FiniteEnum.E(0)));
        assert(!FiniteEnum.E.A.equals(FiniteEnum.E(1)));
        assert(E(2) == E.C);
    }
    function typeStatements() public pure returns (uint) {
        FiniteEnum.E;
        FiniteEnum.LibraryPair;
        Pair[7][];
        return 3;
    }
    function nestedSwap() public pure {
        uint a = 1; uint b = 2; uint c = 3;
        (a, (b, c)) = (c, (a, b));
        assert(a == 3 && b == 1 && c == 2);
    }
    function nestedDiscard() public pure {
        uint a = 3;
        ((, ), ) = ((7, 8), 9);
        (((a, ), )) = ((1, 2), 3);
        assert(a == 1);
    }
    function nestedBytes() public pure {
        bytes memory a; bytes memory b; bytes memory c;
        (a, (b, c)) = ("0", ("1", "2"));
        assert(uint8(a[0]) == 0x30 && uint8(b[0]) == 0x31 && uint8(c[0]) == 0x32);
    }
    function contractKey(FiniteAddress key) public {
        table[key] = 17;
        assert(table[key] == 17);
    }
    function falsePost() public pure {
        uint a = 0;
        (a, (, )) = (1, (2, 3));
        assert(a == 2);
    }
}

contract FiniteTypeFailures {
    function nestedEffect() public pure {
        uint a = 0;
        (a, (, )) = (1, (2 / a, 3));
    }
    function indexedRead() public pure {
        (new uint[](0))[0];
    }
}

contract FiniteAbiOverloads {
    function f(FiniteAddress) internal pure returns (uint) { return 1; }
    function f(address) public pure returns (uint) { return 2; }
}
