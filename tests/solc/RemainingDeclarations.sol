// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract StaticCodeTarget { function value() external pure returns (uint) { return 23; } }
contract StaticCodeConstants {
    bytes constant creation = type(StaticCodeTarget).creationCode;
    bytes constant runtime = type(StaticCodeTarget).runtimeCode;
    bytes stored = type(StaticCodeTarget).runtimeCode;
    function storedLength() external view returns (uint) { return stored.length; }
    function nonempty() external pure returns (bool) { return creation.length > 0 && runtime.length > 0; }
    function firstCreation() external pure returns (uint) { return uint8(creation[0]); }
    function firstRuntime() external pure returns (uint) { return uint8(runtime[0]); }
    function lastRuntime() external pure returns (uint) { return uint8(runtime[runtime.length - 1]); }
    function same() external pure returns (bool) {
        return keccak256(creation) == keccak256(type(StaticCodeTarget).creationCode);
    }
}
contract EnumStructFields {
    enum Small { A, B, C, D }
    enum Larger { A, B, C, D, E }
    struct Record { Small small; Larger large; }
    Record data;
    Small start = Small(1);
    function initial() external view returns (uint) { return uint(start); }
    uint count;
    function set() external { data.small = Small.C; data.large = Larger.E; count = 7; }
    function packed() external view returns (uint) { return abi.encodePacked(data.small).length; }
    function localPacked() external view returns (uint) {
        Small value = data.small;
        return abi.encodePacked(value).length;
    }
    function arrayPacked() external view returns (uint) {
        return abi.encodePacked([data.small][0]).length;
    }
    function wholeArrayPacked() external view returns (uint) {
        Small[] memory values = new Small[](2);
        values[0] = data.small;
        values[1] = Small.B;
        return abi.encodePacked(values).length;
    }
    function values() external view returns (uint) { return uint(data.small) + 10 * uint(data.large); }
    function invalid(uint value) external { count = 8; data.small = Small(value); }
    function saved() external view returns (uint) { return count; }
}
contract MixedStorageResults {
    struct Item { uint value; }
    Item item;
    Item[] items;
    uint count;
    function get() internal returns (uint8, Item storage, uint16) {
        count++;
        item.value = 7;
        return (1, item, 2);
    }
    function broken() internal returns (uint8, Item storage, uint16) {
        count++;
        return (1, items[9], 2);
    }
    function units() internal returns (uint, Item storage, uint) {
        count++;
        return (1 ether, item, 2 minutes);
    }
    function unitsValue() external returns (uint) {
        (uint x,,uint y) = units();
        return x + y;
    }
    function all() external returns (bool) {
        (uint x, Item storage y, uint z) = get();
        (, Item storage y2,) = get();
        (uint x2,,) = get();
        (,,uint z2) = get();
        return x == 1 && y.value == 7 && z == 2 && y2.value == 7 && x2 == 1 && z2 == 2 && count == 4;
    }
    function referenceFailureDespiteHole() external { (uint x,,) = broken(); assert(x == 1); }
    function saved() external view returns (uint) { return count; }
}
contract MixedReturnRefusal {
    struct Item { uint value; }
    Item item;
    function conditional(bool b) internal returns (uint, Item storage, uint) {
        if (b) return (1, item, 2);
        return (3, item, 4);
    }
    function selected(bool b) external returns (uint) { (uint x,,) = conditional(b); return x; }
}

enum OuterChoice { X, Y }
struct SharedRecord { OuterChoice tag; }
function globalChoice(uint x) pure returns (OuterChoice) { return OuterChoice(x); }
contract EnumIdentity {
    enum OuterChoice { A, B, C, D }
    SharedRecord record;
    function good() external returns (uint) { record.tag = globalChoice(1); return uint(record.tag); }
    function packed() external view returns (uint) { return abi.encodePacked(record.tag).length; }
    function own() external pure returns (uint) { return uint(OuterChoice(3)); }
    function invalidGlobal() external { record.tag = globalChoice(3); }
}

contract EnumDecodeRefusal {
    enum Choice { A, B }
    struct Record { Choice choice; }
    function decode(bytes memory input) external pure returns (uint) {
        Record memory record = abi.decode(input, (Record));
        return uint(record.choice);
    }
}
