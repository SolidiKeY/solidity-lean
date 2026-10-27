pragma solidity ^0.8.38;
contract RequireAggregateControls {
    struct Pair { uint16 n; string text; }
    error ArrayRequired(uint[] value, uint n);
    error PairRequired(Pair value, uint n);
    uint marker;
    uint[] values;
    function array() public { uint[] memory a = new uint[](2); a[0] = 7; a[1] = 8; marker = 9; require(false, ArrayRequired(a,3)); }
    function pair() public { marker = 9; require(false, PairRequired(Pair(9,"abc"),3)); }
    function pass() public { uint[] memory a = new uint[](0); require(true, ArrayRequired(a,3)); marker = 7; }
    function get() public view returns (uint) { return marker; }
    function initialize() public { values.push(7); }
    function size() public view returns (uint) { return values.length; }
    function clear() internal returns (uint) { delete values; marker = 99; return 5; }
    function later() public { require(false, ArrayRequired(values,clear())); }
    function laterTrue() public { require(true, ArrayRequired(values,clear())); }
}
