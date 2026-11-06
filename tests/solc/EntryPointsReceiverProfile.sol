// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Paired source-admission controls. Both receiver spellings are valid Solidity.
contract ReceiverProfileBase { uint internal marker; receive() external payable { marker = 17; } }
contract ReceiverProfileInherited is ReceiverProfileBase {
    /// @custom:key box
    function payableReceiver() public { (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); assert(marker == 17); }
    /// @custom:key box
    function bareReceiver() public { (bool ok,) = address(this).call{value:0}(""); assert(ok); assert(marker == 17); }
}
contract ReceiverProfileFallback {
    uint internal marker;
    fallback() external payable { marker = 17; }
    /// @custom:key box
    function payableReceiver() public { (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); assert(marker == 17); }
    /// @custom:key box
    function bareReceiver() public { (bool ok,) = address(this).call{value:0}(""); assert(ok); assert(marker == 17); }
}
contract ReceiverProfileOwn {
    uint internal marker;
    receive() external payable { marker = 17; }
    /// @custom:key box
    function payableReceiver() public { (bool ok,) = payable(address(this)).call{value:0}(""); assert(ok); assert(marker == 17); }
    /// @custom:key box
    function bareReceiver() public { (bool ok,) = address(this).call{value:0}(""); assert(ok); assert(marker == 17); }
}
