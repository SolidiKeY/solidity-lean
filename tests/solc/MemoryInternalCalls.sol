pragma solidity ^0.8.0;
contract MemoryInternalCalls {
    struct Record { uint n; }
    Record stored;
    function touch(uint[] memory a, uint[] memory b, uint v) internal pure returns (uint r) {
        a[0] = v;
        require(b[0] == v);
        a = new uint[](2);
        a[0] = 88;
        require(b[0] == v);
        return b[0] + 1;
    }
    function nested(uint[] memory a) internal pure returns (uint r) { return touch(a, a, 7); }
    function echo(uint[] memory a) internal pure returns (uint[] memory r) { r = a; }
  function escapeLocal(uint[] memory a) internal pure returns (uint[] memory r) {
    uint[] memory owned = new uint[](2);
    owned[0] = 33;
    r = owned;
    a = new uint[](1);
    a[0] = 44;
  }
    function fresh(uint n) internal pure returns (uint[] memory r) { r = new uint[](n); r[0] = 11; }
    function forwarded(uint n) internal pure returns (uint[] memory r) { r = fresh(n); }
    function record(Record memory a) internal pure returns (Record memory r) { a.n = 9; r = a; }
    function first(uint[] memory a) internal pure returns (uint r) { return a[0]; }
    function signedEcho(uint[] memory a, int delta) internal pure returns (int r) { a[0] = 19; return delta; }
    function boolEcho(uint[] memory a, bool flag) internal pure returns (bool r) { require(a[0] == 19); return flag; }
    function make(uint n) internal pure { uint[] memory a = new uint[](n); require(a.length == n); }
    function largeCost() external pure returns (uint) { make(4096); return 4097; }
    function bump(uint[] memory a) internal pure { a[0] = 17; }
    function fail() internal pure { require(false); uint[] memory unreachable = new uint[](4); }
    function voidCall() external pure returns (uint, uint) {
        uint marker = 42;
        uint[] memory xs = new uint[](1);
        bump(xs);
        require(xs[0] == 17 && marker == 42);
        return (xs[0], marker);
    }
    function directCopy() external returns (uint, uint) {
        stored.n = 4;
        Record memory same = record(stored);
        require(same.n == 9 && stored.n == 4);
        return (same.n, stored.n);
    }
    function forwarding() external pure returns (uint) {
        uint[] memory xs = forwarded(1);
        xs[0] = 21;
        require(xs[0] == 21);
        return xs[0];
    }
    function mutation() external pure returns (uint, uint, uint) {
        uint[] memory xs = new uint[](1);
        uint untouched = 42;
        uint result = nested(xs);
        require(result == 8 && xs[0] == 7 && untouched == 42);
        return (result, xs[0], untouched);
    }
    function references() external pure returns (uint, uint) {
        uint[] memory xs = fresh(2);
        uint[] memory same = echo(xs);
        same[0] = 12;
        require(xs[0] == 12 && same.length == 2);
        return (xs[0], same.length);
    }
    function copies() external returns (uint, uint, uint) {
        stored.n = 4;
        Record memory independent = stored;
        Record memory same = record(independent);
        require(independent.n == 9 && same.n == 9 && stored.n == 4);
        return (independent.n, same.n, stored.n);
    }
    function branches(bool take) external pure returns (uint) {
        uint[] memory xs = new uint[](1);
        if (take) { uint result = nested(xs); require(result == 8); }
        else { uint result = nested(xs); require(result == 8); }
        require(xs[0] == 7);
        return xs[0];
    }
    function boundsFailure() external pure returns (uint) {
        uint[] memory xs = new uint[](0);
        return first(xs);
    }
    function calleeFailure() external pure {
        uint[] memory xs = new uint[](0);
        fail();
        uint[] memory unreachable = new uint[](5);
    }
    function failedReturnArgument() external pure returns (uint[] memory) {
        uint[] memory empty = new uint[](0);
        return fresh(empty[0]);
    }
    function callerOwnership() external pure returns (uint, uint, uint, uint, uint, uint) {
        uint marker = 42;
        uint[] memory caller = new uint[](1);
        caller[0] = 5;
        uint[] memory shared = echo(caller);
        uint[] memory escaped = escapeLocal(caller);
        bump(caller);
        uint[] memory later = fresh(1);
        require(caller[0] == 17 && shared[0] == 17 && escaped[0] == 33 &&
            escaped.length == 2 && later[0] == 11 && marker == 42);
        return (caller[0], shared[0], escaped[0], escaped.length, later[0], marker);
    }

    function discardedReturn() external pure returns (uint, uint) {
        uint marker = 42;
        uint[] memory xs = new uint[](1);
        nested(xs);
        require(xs[0] == 7 && marker == 42);
        return (xs[0], marker);
    }
    function primitiveTypes() external pure returns (int, bool, uint, uint) {
        uint marker = 42;
        uint[] memory xs = new uint[](1);
        int value = signedEcho(xs, -3);
        bool take = boolEcho(xs, true);
        if (take) { require(value == -3); } else { revert(); }
        require(xs[0] == 19 && marker == 42);
        return (value, take, xs[0], marker);
    }

}
