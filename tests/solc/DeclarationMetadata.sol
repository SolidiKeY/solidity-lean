// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

interface MetadataBase { function inherited(uint256) external; }
interface MetadataChild is MetadataBase { function own(address) external; }
interface MetadataEmpty is MetadataBase {
    receive() external payable;
    fallback() external;
}
interface MetadataMulti is MetadataBase {
    function choice(uint256) external;
    function choice(address) external;
}
contract MetadataForeign { error Problem(bool flag); }

contract DeclarationMetadata {
    uint256 receiverCount;
    enum Kind { First, Second }
    type Value is uint64;
    struct Item { uint8 n; address who; }
    error Problem(Kind kind, Value value, address who);
    event Changed(Item item);
    event Hidden(uint256 value) anonymous;

    /// @custom:key box
    function contractName() public pure {
        bytes memory name = bytes(type(DeclarationMetadata).name);
        assert(name.length == 19);
        assert(name[0] == 0x44 && name[18] == 0x61);
    }

    /// @custom:key box
    function interfaceOwnOnly() public pure {
        assert(type(MetadataChild).interfaceId == MetadataChild.own.selector);
        assert(type(MetadataEmpty).interfaceId == bytes4(0));
        assert(type(MetadataChild).interfaceId !=
            (MetadataBase.inherited.selector ^ MetadataChild.own.selector));
        assert(type(MetadataMulti).interfaceId ==
            (bytes4(keccak256("choice(uint256)")) ^ bytes4(keccak256("choice(address)"))));
    }

    /// @custom:key box
    function errorSelector() public pure {
        // Enum and value-type parameters use their underlying ABI types.
        assert(Problem.selector == bytes4(keccak256("Problem(uint8,uint64,address)")));
        assert(MetadataForeign.Problem.selector == bytes4(keccak256("Problem(bool)")));
    }

    /// @custom:key box
    function eventSelector() public pure {
        // An event's tuple parameter expands its struct members canonically.
        assert(Changed.selector == keccak256("Changed((uint8,address))"));
    }

    /// @custom:key box
    function overloaded(uint256) public pure {}
    /// @custom:key box
    function overloaded(address) public pure {}

    function callback(uint256) public pure {}
    function callbackAddress(address) public pure {}

    function receiver() internal returns (address) {
        receiverCount += 1;
        return address(this);
    }

    /// @custom:key box
    function receiverEffects() public {
        receiverCount = 0;
        bytes4 value = DeclarationMetadata(receiver()).callback.selector;
        assert(receiverCount == 1);
        assert(value == this.callback.selector);
    }

    /// @custom:key box
    function functionMetadata() public view {
        function(uint256) external pure first = this.callback;
        assert(first.selector == this.callback.selector);
        assert(first.address == address(this));
    }

    /// @custom:key box
    function overloadSelection() public pure {
        overloaded(uint256(0));
        overloaded(address(0));
    }

    /// @custom:key box
    function falseMetadata() public pure {
        assert(type(MetadataEmpty).interfaceId == bytes4(uint32(1)));
    }
}
