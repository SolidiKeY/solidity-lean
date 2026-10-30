// SPDX-License-Identifier: MIT
pragma solidity >=0.8.0;
contract PaymentReferences {
    fallback() external payable {}
    uint count;
    function receiver() internal returns (address payable) {
        count += 1;
        return payable(address(9));
    }
    /// @custom:key requires count == 0
    /// @custom:key ensures count == 2
    function discardedEffects() public {
        receiver().send;
        receiver().transfer;
    }
    function rejectingReceiver() internal pure returns (address payable) {
        revert("receiver");
    }
    /// @custom:key box
    /// @custom:key ensures false
    function discardedFailure() public {
        rejectingReceiver().transfer;
    }
    /// @custom:key ensures count == \old(count)
    function discardedSelf() public {
        payable(this).transfer;
    }
}
contract ActualPaymentDispatch {
    fallback() external payable {}
    function actual() public { payable(this).transfer(0); }
    function parenthesized() public { (payable(this).transfer)(0); }
    function conditional(bool c) public {
        (c ? payable(this) : payable(this)).transfer(0);
    }
}
