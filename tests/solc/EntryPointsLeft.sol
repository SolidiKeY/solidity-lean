// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
contract NominalGetters {
    enum Shade { Zero, One, Two }
    Shade public shade;
    mapping(uint => Shade) public shades;
    NominalGetters public owner;
    struct Entry { Shade shade; address owner; uint[] omitted; mapping(uint => uint) hidden; }
    Entry public entry;
    /// @custom:key box
    function enumScalar() public { shade = Shade.Two; assert(this.shade() == Shade.Two); }
    /// @custom:key box
    function enumMapping() public { shades[7] = Shade.Two; assert(this.shades(7) == Shade.Two); }
    /// @custom:key box
    function enumStruct() public {
        entry.shade = Shade.Two; entry.owner = address(this);
        try this.entry() returns (Shade s, address a) { assert(s == Shade.Two); assert(a == address(this)); }
        catch { assert(false); }
    }
    /// @custom:key box
    function contractScalar() public { owner = this; assert(address(this.owner()) == address(this)); }
    /// @custom:key box
    function falseEnum() public { shade = Shade.Two; assert(this.shade() == Shade.One); }
}
contract ReceiverBase {
    uint internal marker;
    receive() external payable virtual { marker = 17; }
}
contract InheritedReceiver is ReceiverBase {
    /// @custom:key box
    function positive() public { marker = 0; (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); assert(marker == 17); }
    /// @custom:key box
    function falseObservation() public { marker = 0; (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); assert(marker == 18); }
    /// @custom:key box
    function stipendRefusal() public { payable(address(this)).transfer(0); assert(marker == 17); }
}
contract FallbackBase {
    uint internal marker;
    fallback() external payable { marker = 23; }
}
contract InheritedFallback is FallbackBase {
    /// @custom:key box
    function positive() public { marker = 0; (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); assert(marker == 23); }
    /// @custom:key box
    function falseObservation() public { marker = 0; (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); assert(marker == 24); }
}
contract ExternalBase {
    function target(uint x) external pure virtual returns(uint) { return x; }
}
contract RenamedExternal is ExternalBase {
    /// @custom:key box
    function positive() public view { function(uint) external pure returns(uint) h = this.target; assert(h(3) == 3); assert(h.selector == ExternalBase.target.selector); }
    /// @custom:key box
    function falseObservation() public view { function(uint) external pure returns(uint) h = this.target; assert(h(3) == 4); }
}
contract RefusedGetters {
    bytes public data;
    string public text;
    function() external public action;
    /// @custom:key box
    function referenceBytes() public view { bytes memory b = this.data(); assert(b.length == 0); }
    /// @custom:key box
    function referenceString() public view { string memory s = this.text(); assert(bytes(s).length == 0); }
    /// @custom:key box
    function functionResult() public view { function() external f = this.action(); assert(f.address == address(this)); }
}

contract ReceivePriorityBase {
    uint internal marker;
    receive() external payable virtual { marker = 31; }
}
contract ReceivePriority is ReceivePriorityBase {
    fallback() external payable { marker = 99; }
    /// @custom:key box
    function positive() public { marker = 0; (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); assert(marker == 31); }
}
contract ReceiveOverride is ReceiverBase {
    receive() external payable override { marker = 29; }
    /// @custom:key box
    function positive() public { marker = 0; (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); assert(marker == 29); }
}
contract NonpayableFallbackBase {
    fallback() external {}
}
contract NonpayableFallbackRefusal is NonpayableFallbackBase {
    /// @custom:key box
    function entry() public { (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); }
}
contract ModifiedReceiverBase {
    modifier guarded() { _; }
    receive() external payable guarded {}
}
contract ModifiedReceiverRefusal is ModifiedReceiverBase {
    /// @custom:key box
    function entry() public { (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); }
}
contract HelperReceiverBase {
    uint marker;
    function helper() internal { marker = 1; }
    receive() external payable { helper(); }
}
contract HelperReceiverRefusal is HelperReceiverBase {
    /// @custom:key box
    function entry() public { (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); }
}
contract ByteFallbackBase {
    fallback(bytes calldata input) external payable returns(bytes memory) { return input; }
}
contract ByteFallbackRefusal is ByteFallbackBase {
    /// @custom:key box
    function entry() public { (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); }
}
contract NominalDispatchRefusal {
    NominalGetters public owner;
    function clean() external pure returns(address) { return address(7); }
    /// @custom:key box
    function entry() public view { function() external pure returns(address) h = this.clean; assert(h() == address(7)); }
}
contract ExternalOverride is ExternalBase {
    function target(uint x) external pure override returns(uint) { return x + 1; }
    /// @custom:key box
    function positive() public view { function(uint) external pure returns(uint) h = this.target; assert(h(3) == 4); }
}
contract ExternalOverloadCollisionRefusal {
    function target(uint x) external pure returns(uint) { return x; }
    function target(address a) internal pure returns(address) { return a; }
    /// @custom:key box
    function positive() public view { function(uint) external pure returns(uint) h = this.target; assert(h(3) == 3); }
}

contract ExternalOverloads {
    function target(uint x) external pure returns(uint) { return x; }
    function target(bool b) internal pure returns(bool) { return b; }
    /// @custom:key box
    function positive() public view {
        function(uint) external pure returns(uint) h = this.target;
        assert(h(3) == 3); assert(h.selector == bytes4(keccak256("target(uint256)")));
    }
}
contract OwnHelperReceiver {
    uint internal marker;
    function helper() internal { marker = 37; }
    receive() external payable { helper(); }
    /// @custom:key box
    function positive() public { marker = 0; (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); assert(marker == 37); }
}
contract NominalKeyDispatchRefusal {
    mapping(NominalGetters => uint) public values;
    function clean(address) external pure returns(uint) { return 7; }
    /// @custom:key box
    function entry() public view { function(address) external pure returns(uint) h = this.clean; assert(h(address(this)) == 7); }
}
contract FrameReceiverBase {
    uint internal marker;
    address internal sender;
    receive() external payable { marker = msg.value; sender = msg.sender; }
}
contract InheritedFrameReceiver is FrameReceiverBase {
    /// @custom:key box
    /// @custom:key requires address(this).balance >= 1
    function positive() public { marker = 0; (bool ok,) = payable(address(this)).call{value:1}(""); assert(ok); assert(marker == 1); assert(sender == address(this)); }
}
contract FrameFallbackBase {
    uint internal marker;
    address internal sender;
    fallback() external payable { marker = msg.value; sender = msg.sender; }
}
contract InheritedFrameFallback is FrameFallbackBase {
    /// @custom:key box
    /// @custom:key requires address(this).balance >= 1
    function positive() public { marker = 0; (bool ok,) = payable(address(this)).call{value:1}(""); assert(ok); assert(marker == 1); assert(sender == address(this)); }
}
contract RevertingReceiverBase {
    uint internal marker;
    receive() external payable { marker = 99; revert(); }
}
contract InheritedRollback is RevertingReceiverBase {
    /// @custom:key box
    function positive() public { marker = 7; (bool ok,) = payable(address(this)).call{value:0}(""); assert(!ok); assert(marker == 7); }
}

contract ContractKeyGetter {
    mapping(NominalGetters => uint8) public values;
    /// @custom:key box
    function positive() public {
        NominalGetters key = NominalGetters(address(this));
        values[key] = 11; assert(this.values(key) == 11);
    }
}
