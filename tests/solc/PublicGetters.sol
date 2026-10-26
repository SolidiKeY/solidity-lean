// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface ICountGetter {
    function count() external view returns (uint32);
}
contract GetterBase {
    uint16 public inheritedValue;
    function inherited(uint8 x) public pure returns (uint8) { return x; }
}
contract PublicGetters is GetterBase, ICountGetter {
    uint32 public override count;
    int16 public debt;
    address public holder;
    bool public ready;
    bytes2 public marker;
    uint public constant LIMIT = 9;
    uint public immutable fixedValue = 11;
    mapping(address who => mapping(uint16 kind => uint32 quantity)) public allowances;
    mapping(bool flag => uint amount) public flags;
    uint32[] public items;
    uint16[2] public fixedItems;
    mapping(uint key => uint16[] values) public sequences;
    struct Entry {
        uint32 value;
        bool live;
        uint[] omittedArray;
        mapping(uint => uint) omittedMap;
    }
    Entry public entry;
    address[] private receivers;

    // Filled with the actual count declaration ID by the fixture generator.
    function solcGetter27() internal pure returns (uint32) { return 99; }
    uint solcGetterArg54_0;

    /// @custom:key box
    function scalar() public {
        count = 37;
        uint32 observed = this.count();
        assert(observed == 37);
        assert(count == 37);
    }
    /// @custom:key box
    function viaInterface() public {
        count = 41;
        uint32 observed = ICountGetter(address(this)).count();
        assert(observed == 41);
    }
    /// @custom:key box
    function primitives() public {
        debt = -5; holder = address(this); ready = true; marker = 0x1234;
        assert(this.debt() == -5);
        assert(this.holder() == address(this));
        assert(this.ready());
        assert(this.marker() == bytes2(0x1234));
        assert(this.LIMIT() == 9);
        assert(this.fixedValue() == 11);
    }
    /// @custom:key box
    function nestedMapping() public {
        allowances[address(this)][2] = 23;
        assert(this.allowances({kind: 2, who: address(this)}) == 23);
        assert(allowances[address(this)][2] == 23);
    }
    /// @custom:key box
    function boolKeys() public {
        flags[true] = 8; flags[false] = 7;
        assert(this.flags(true) == 8);
        assert(this.flags(false) == 7);
    }
    /// @custom:key box
    function arrays() public {
        uint n = items.length;
        items.push(19);
        assert(this.items(n) == 19);
        fixedItems[1] = 33;
        assert(this.fixedItems(1) == 33);
        uint m = sequences[2].length;
        sequences[2].push(7);
        assert(this.sequences(2, m) == 7);
    }
    /// @custom:key box
    function structFields() public {
        entry.value = 7; entry.live = true;
        try this.entry() returns (uint32 value, bool live) {
            assert(value == 7); assert(live);
        } catch { assert(false); }
    }
    /// @custom:key box
    function inheritedGetters() public {
        inheritedValue = 17;
        assert(this.inheritedValue() == 17);
        assert(this.inherited(5) == 5);
        bytes memory payload = abi.encodeCall(this.inherited, (uint8(5)));
        assert(bytes4(payload) == this.inherited.selector);
    }
    /// @custom:key box
    function fixedBounds() public {
        try this.fixedItems(2) returns (uint16 value) {
            value; assert(false);
        } catch (bytes memory reason) { assert(reason.length == 0); }
    }
    /// @custom:key box
    function identity() public view {
        assert(this.count.address == address(this));
        assert(this.count.selector == ICountGetter.count.selector);
        bytes memory payload = abi.encodeCall(this.allowances, (address(this), uint16(2)));
        assert(bytes4(payload) == this.allowances.selector);
    }
    /// @custom:key box
    function selectorRead(uint i) external view returns (bytes4) {
        return PublicGetters(receivers[i]).count.selector;
    }
    /// @custom:key box
    function selectorBounds() public {
        delete receivers;
        try this.selectorRead(0) returns (bytes4 selected) { selected; assert(false); }
        catch Panic(uint code) { assert(code == 0x32); }
    }
    /// @custom:key box
    function falseBoundsPanic() public {
        try this.fixedItems(2) returns (uint16 value) { value; assert(false); }
        catch (bytes memory reason) { assert(reason.length == 36); }
    }
    /// @custom:key box
    function falseScalar() public {
        count = 37;
        assert(this.count() == 38);
    }
}

// These getters must be refused as a whole: bytes/string remain returned
// struct fields, rather than being incorrectly omitted like ordinary arrays.
contract GetterReferences {
    bytes public data;
    struct Mixed { uint value; string text; uint[] omitted; }
    Mixed public mixed;
    function localBytes() public view { uint n = data.length; assert(data.length == n); }
    function rejectedBytes() public view { bytes memory result = this.data(); result; }
    function rejectedMixed() public view {
        try this.mixed() returns (uint value, string memory text) { value; text; } catch {}
    }
}
contract GetterReturnBase {
    uint value;
    constructor() { value = 1; return; }
}
contract GetterCtorCollision is GetterReturnBase {
    // Filled with the actual base constructor ID, not a guessed prefix.
    function solcCtorBody721() internal { value = 99; }
    constructor() { assert(value == 1); }
}
contract GetterCtorFalse is GetterReturnBase {
    constructor() { assert(value == 99); }
}

// Import renaming must also reserve the printed struct-constructor name.
struct GetterBox { uint value; }
contract GetterCtorStructAlias is GetterReturnBase {
    constructor() {
        GetterBox memory box = GetterBox(7);
        assert(box.value == 7); assert(value == 1);
    }
}

contract GetterFunctionSlot {
    function () external public stored;
    function nonzero() external {}
    function falseStoredSelector() public {
        stored = this.nonzero;
        assert(stored.selector == this.stored.selector);
    }
    function getterSelector() public view { assert(this.stored.selector == bytes4(0xe582dd31)); }
}

// Runtime bytes-to-fixed-bytes prefix conversion, including lazy/effectful sources.
contract GetterBytePrefixes {
    uint calls;
    function make() internal returns (bytes memory result) { calls++; result = hex"1234"; }
    function broken() internal pure returns (bytes memory result) { require(false); result = hex""; }
    function emptyPrefix() public pure { bytes memory data = hex""; assert(bytes4(data) == bytes4(0)); }
    function shortPrefix() public pure { bytes memory data = hex"12"; assert(bytes4(data) == bytes4(0x12000000)); }
    function leadingZeroPrefix() public pure { bytes memory data = hex"0012"; assert(bytes4(data) == bytes4(0x00120000)); }
    function longPrefix() public pure { bytes memory data = hex"0102030405"; assert(bytes4(data) == bytes4(0x01020304)); }
    function evaluateOnce() public {
        calls = 0; bytes4 value = bytes4(make());
        assert(calls == 1 && value == bytes4(0x12340000));
    }
    function lazyPrefix() public {
        calls = 0;
        assert(!(false && bytes4(make()) == bytes4(0)));
        assert(true || bytes4(broken()) == bytes4(0));
        assert(calls == 0);
    }
}
