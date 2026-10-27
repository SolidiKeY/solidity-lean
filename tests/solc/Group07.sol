pragma solidity ^0.8.38;
contract Group07 {
    struct S { uint x; }
    S[] data;
    S[][] rows;
    function fail() internal pure returns (uint) { revert(); }
    function lazyDiscard() public {
        false ? (data.push().x = 1, 0) : (0, 0);
        assert(data.length == 0);
    }
    function orderedDiscard() public { (fail(), data.push().x = 1); }
    function checkedNegation() public pure { -(type(int8).min); }
    function uncheckedNegation() public pure { unchecked { (-(type(int8).min)); } }
    function lazyTuple() public pure returns (uint a, uint b) {
        (a, b) = true ? (1, 2) : (uint(3) / a, 4);
        assert(a == 1 && b == 2);
    }
    function overlappingMemory() public pure {
        uint[2] memory m;
        (m[0], m[1], m[0]) = (1, 2, 3);
        assert(m[0] == 1 && m[1] == 2);
    }
    function literalStringChoice() public pure {
        string memory s = false ? "a" : (true ? "bc" : "d");
        assert(bytes(s).length == 2);
    }
    function set(S storage s, uint y) internal { s.x = y; }
    function pushReference() public {
        set(data.push(), 17);
        uint y = 23; data.push().x = y;
        assert(data.length == 2 && data[0].x == 17 && data[1].x == 23);
    }
    function pushIndexOnce() public {
        rows.push(); uint i = 0; set(rows[i++].push(), 31);
        assert(i == 1 && rows[0].length == 1 && rows[0][0].x == 31);
    }
    function effectfulPushReceiver() public {
        rows.push(); uint y = 0; rows[y++].push().x = y;
    }
    function scalarDelete() public pure {
        uint n = 3; bool b = true; delete n; delete b;
        assert(n == 0 && !b);
    }
}
