pragma solidity ^0.8.38;
error ArrayError(uint[] a, uint n);
error NestedError(uint[][] a);
contract AggregateErrorControls {
    struct ErrorPair { uint16 a; string b; }
    error PairError(uint n, ErrorPair p, int8 z);
    uint[] a;
    ErrorPair p;
    uint counter;
    uint[][] nested;
    uint index;
    function initialize() public { a.push(7); p.a = 9; p.b = "abc"; nested.push(); nested[0].push(7); nested.push(); nested[1].push(8); }
    function length() public view returns (uint) { return a.length; }
    function field() public view returns (uint16) { return p.a; }
    function count() public view returns (uint) { return counter; }
    function context() public payable returns (uint) { return uint160(msg.sender) + msg.value; }
    function clearArray() internal returns (uint) { delete a; counter++; return 5; }
    function clearPair() internal returns (uint) { delete p; counter++; return 5; }
    function arrayStorage() public { revert ArrayError(a, clearArray()); }
    function arrayNamed() public { revert ArrayError({n: clearArray(), a: a}); }
    function pairStorage() public { revert PairError(clearPair(), p, int8(-1)); }
    function pairNamed() public { revert PairError({p: p, z: int8(-1), n: clearPair()}); }
    function arrayEmpty() public pure { uint[] memory v = new uint[](0); revert ArrayError(v, 3); }
    function arrayMemory() public pure { uint[] memory v = new uint[](2); v[0] = 7; v[1] = 8; revert ArrayError(v, 3); }
    function pairMemory() public pure { revert PairError({z: int8(-1), p: ErrorPair({b: "abc", a: 9}), n: 3}); }
    function pairEmpty() public pure { revert PairError(3, ErrorPair(9, ""), int8(-1)); }
    function arrayCalldata(uint[] calldata v) public pure { revert ArrayError({n: 3, a: v}); }
    function pairCalldata(ErrorPair calldata v) public pure { revert PairError({z: int8(-1), p: v, n: 3}); }
    function mutate(uint[] memory v) internal pure returns (uint) { v[0] = 11; return 5; }
    function memoryLater() public pure { uint[] memory v = new uint[](1); v[0] = 7; revert ArrayError(v, mutate(v)); }
    function namedMemoryLater() public pure { uint[] memory v = new uint[](1); v[0] = 7; revert ArrayError({n: mutate(v), a: v}); }
    function nestedMemory() public pure { uint[][] memory v = new uint[][](2); v[0] = new uint[](1); v[0][0] = 7; v[1] = new uint[](0); revert NestedError(v); }
    function pairMemoryLater() public pure { ErrorPair memory v = ErrorPair(9, "abc"); revert PairError(v.a++, v, int8(-1)); }
    function pairNamedMemoryLater() public pure { ErrorPair memory v = ErrorPair(9, "abc"); revert PairError({p: v, z: int8(-1), n: v.a++}); }
    function changeIndex() internal returns (uint) { index = 1; nested[0][0] = 11; return 5; }
    function indexedStorage() public { revert ArrayError(nested[index], changeIndex()); }
    function indexedNamed() public { revert ArrayError({a: nested[index], n: changeIndex()}); }
    function fail() internal pure returns (uint) { assert(false); return 0; }
    function beforeEncoding() public { revert ArrayError(a, fail()); }
}
