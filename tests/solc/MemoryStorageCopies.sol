// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.34;
contract MemoryStorageCopies {
    struct Record { uint n; bool flag; int signed; }
    struct Holder { Record item; }
    uint[] values;
    int[] signedValues;
    bool[] flags;
    Record stored;
    Holder holder;
    mapping(uint => Record) records;
    uint[][] rows;
    mapping(uint => uint[]) arrayRecords;
    struct FixedHolder { uint[2] pair; }
    uint[2] fixedPair;
    FixedHolder fixedBox;
    mapping(uint => uint[2]) fixedPairs;
    uint[3] fixedPadded;
    uint[] fixedDynamic;
    uint[][] fixedRows;
    function fixedShape() external returns (uint, uint, uint, uint, uint, uint) {
        uint[2] memory xs = [uint(31), uint(47)];
        uint[] memory old = new uint[](3); old[0] = 8; old[1] = 9; old[2] = 88;
        fixedDynamic = old;
        fixedPadded[2] = 88;
        fixedPadded = xs;
        fixedDynamic = xs;
        xs[0] = 99;
        return (fixedPadded[0], fixedPadded[1], fixedPadded[2],
                fixedDynamic.length, fixedDynamic[0], fixedDynamic[1]);
    }
    function fixedBadDestination() external {
        uint[2] memory xs = [uint(31), uint(47)];
        fixedRows[0] = xs;
    }
    function lifecycle() external returns (uint, uint, uint, uint, uint, uint, uint, uint, uint) {
        uint[2] memory xs;
        fixedPair = xs;
        require(fixedPair[0] == 0 && fixedPair[1] == 0);
        xs[0] = 31; xs[1] = 47;
        fixedPair = xs; fixedPadded = xs;
        uint[] memory old = new uint[](3); old[0] = 8; old[1] = 9; old[2] = 88;
        fixedDynamic = old; fixedDynamic = xs;
        xs[0] = 99;
        Record memory r; r.n = 77; stored = r; r.n = 88;
        require(fixedPair[0] == 31 && fixedPair[1] == 47);
        require(fixedDynamic.length == 2 && fixedDynamic[0] == 31 && fixedDynamic[1] == 47);
        require(stored.n == 77);
        return (fixedPair[0], fixedPair[1], fixedPadded[2], fixedDynamic.length,
                fixedDynamic[0], fixedDynamic[1], stored.n, xs[0], r.n);
    }
    function mixedCopy() external returns (uint, uint, uint, uint, uint, uint) {
        uint[2] memory xs = [uint(31), uint(47)];
        uint[] memory ys = new uint[](2); ys[0] = 91; ys[1] = 92;
        Record memory r; r.n = 77;
        fixedPair = xs; values = ys; stored = r;
        return (fixedPair[0], fixedPair[1], values.length, values[0], values[1], stored.n);
    }
    function fixedCopy(bool flag) external returns (uint, uint, uint, uint, uint, uint, uint) {
        uint[2] memory xs = [uint(31), uint(47)];
        fixedPair = xs;
        if (flag) fixedBox.pair = xs;
        fixedPairs[5] = xs;
        xs[0] = 99;
        return (fixedPair[0], fixedPair[1], fixedBox.pair[0], fixedBox.pair[1],
                fixedPairs[5][0], fixedPairs[5][1], xs[0]);
    }
    function exercise(uint n) external returns (uint, uint, uint, uint, uint) {
        require(n == 3);
        uint[] memory xs = new uint[](n);
        xs[0] = 7; xs[1] = 8; xs[2] = 9;
        values = xs;
        xs[0] = 99;
        require(values[0] == 7 && values.length == 3);
        uint[] memory ys = new uint[](1); ys[0] = 4;
        values = ys;
        require(values.length == 1 && values[0] == 4);
        values = xs;
        require(values[0] == 99 && values[2] == 9);
        uint[] memory zs = new uint[](0); values = zs;
        require(values.length == 0);
        values = ys; ys[0] = 55;
        require(values[0] == 4);
        Record memory r;
        r.n = 12; r.flag = true; r.signed = -3;
        stored = r; r.n = 77; holder.item = r; records[3] = r;
        r.flag = false;
        require(stored.n == 12 && stored.flag && stored.signed == -3);
        require(holder.item.n == 77 && holder.item.flag);
        require(records[3].n == 77 && records[3].flag);
        return (values.length, values[0], stored.n, holder.item.n, records[3].n);
    }
    function signedAndBool() external returns (int, int, bool, bool) {
        int[] memory xs = new int[](2); xs[0] = -7; xs[1] = 9; signedValues = xs;
        xs[0] = -11; require(signedValues[0] == -7);
        bool[] memory bs = new bool[](2); bs[0] = true; flags = bs;
        bs[0] = false; require(flags[0] && !flags[1]);
        return (signedValues[0], signedValues[1], flags[0], flags[1]);
    }
    function outOfBounds() external {
        uint[] memory xs = new uint[](3);
        rows[0] = xs;
    }
    function runtimeLength(uint n) external returns (uint, uint, uint) {
        require(n <= 3);
        uint[] memory xs = new uint[](n);
        if (n > 0) xs[0] = 17;
        values = xs;
        arrayRecords[5] = xs;
        if (n > 0) xs[0] = 99;
        require(values.length == n && arrayRecords[5].length == n);
        if (n > 0) require(values[0] == 17 && arrayRecords[5][0] == 17);
        return (values.length, n == 0 ? 0 : values[0], n == 0 ? 0 : xs[0]);
    }
    function unchanged() external view returns (uint, uint) { return (values.length, values[0]); }
}
