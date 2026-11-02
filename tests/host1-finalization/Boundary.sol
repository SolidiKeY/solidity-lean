// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
contract Child {
    uint256 public stored = 42;
    event Seed(uint256 indexed value);
    constructor() payable { emit Seed(0x1122334400000000000000000000000000000000000000000000000000000055); }
    function die(address payable beneficiary) external payable { selfdestruct(beneficiary); }
}
contract Failing {
    uint256 public stored = 42;
    constructor() payable { assembly ("memory-safe") { mstore(0, 0xdeadbeef) revert(28, 4) } }
}
contract ConstructorDie {
    uint256 public stored = 42;
    constructor(address payable beneficiary) payable { selfdestruct(beneficiary); }
}
contract Boundary {
    uint256 public mark = 7;
    event Spawn(address value);
    event Seen(uint256 value);
    function createAndDestroy(address payable beneficiary) external payable returns (address) {
        Child c = new Child{value: msg.value}();
        emit Spawn(address(c));
        c.die(beneficiary);
        return address(c);
    }
    function createDestroyAndRevert(address payable beneficiary) external payable {
        Child c = new Child{value: msg.value}();
        emit Spawn(address(c));
        c.die(beneficiary);
        assembly ("memory-safe") { mstore(0, 0xdeadbeef) revert(28, 4) }
    }
    function catchChildRevert(address payable beneficiary) external payable returns (bytes memory) {
        try this.createDestroyAndRevert{value: msg.value}(beneficiary) { return hex"00"; }
        catch (bytes memory data) { return data; }
    }
    function createAlive() external payable returns (address) {
        Child c = new Child{value: msg.value}();
        emit Spawn(address(c));
        return address(c);
    }
    function create2AndDestroy(address payable beneficiary, bytes32 salt) external payable returns (address) {
        Child c = new Child{value: msg.value, salt: salt}();
        emit Spawn(address(c));
        c.die(beneficiary);
        return address(c);
    }
    function transientWrite(uint256 value) external returns (uint256 result) {
        assembly ("memory-safe") { tstore(99, value) result := tload(99) }
        emit Seen(result);
    }
    function transientRead() external view returns (uint256 result) {
        assembly ("memory-safe") { result := tload(99) }
    }
    function touchEmpty(address payable target) external { (bool ok,) = target.call(""); require(ok); }
}
