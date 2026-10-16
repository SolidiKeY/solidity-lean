pragma solidity ^0.8.26;

contract ReferenceParameters {
    struct Token { uint value; }
    Token tok;
    uint[] values;
    mapping(uint => uint) counts;

    function first(uint[] memory a) internal pure returns (uint) { return a[0]; }
    function set(Token storage t, uint v) internal { t.value = v; }
    function credit(mapping(uint => uint) storage m, uint k) internal { m[k] = 1; }
    function get(uint[] storage a) internal pure returns (uint[] storage r) { r = a; }
    function root() internal view returns (uint[] storage r) { r = values; }
    function grow(uint[] storage a) internal { a.push(1); }
    function mutate() internal returns (uint) { values[0] = 9; return 0; }
    function observed(uint before, uint[] memory a, uint ignored) internal pure returns (uint) {
        assert(before == 1); assert(a[0] == 1); return a[0];
    }
    function allocateUse(uint[] memory a) internal pure { assert(a.length == 2); }

    function storageAndMemory() public {
        uint[] memory xs = new uint[](1); xs[0] = 7;
        uint r = first(xs); assert(r == 7);
        set(tok, 4); assert(tok.value == 4);
        credit(counts, 3); assert(counts[3] == 1);
    }

    function copiesBeforeEffects() public {
        delete values;
        values.push(1);
        uint r = observed(values[0], values, mutate());
        assert(r == 1); assert(values[0] == 9);
    }

    function nestedStorageReturn() public {
        delete values;
        grow(root()); assert(values.length >= 1);
        get(values).push(4);
        assert(values[values.length - 1] == 4);
    }

    function allocationArgument() public pure { allocateUse(new uint[](2)); }

    function initializedInput(uint[] memory a) public pure { assert(a.length >= 0); }
}
