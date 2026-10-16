// Source: https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/common-patterns.rst
// Changes: the custom errors are dropped, `revert Err()` becomes `revert()`; block.timestamp is
// the timeNow state variable.
// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.4;

contract AccessRestriction {
    // These will be assigned at the construction
    // phase, where `msg.sender` is the account
    // creating this contract.
    uint timeNow;
    address public owner = msg.sender;
    uint public creationTime = timeNow;

    // Now follows a list of errors that
    // this contract can generate together
    // with a textual explanation in special
    // comments.


    // Modifiers can be used to change
    // the body of a function.
    // If this modifier is used, it will
    // prepend a check that only passes
    // if the function is called from
    // a certain address.
    modifier onlyBy(address account)
    {
        if (msg.sender != account)
            revert();
        // Do not forget the "_;"! It will
        // be replaced by the actual function
        // body when the modifier is used.
        _;
    }

    /// Make `newOwner` the new owner of this
    /// contract.
    /// @custom:key ensures \old(owner) == msg.sender && owner == newOwner
    function changeOwner(address newOwner)
        public
        onlyBy(owner)
    {
        owner = newOwner;
    }

    modifier onlyAfter(uint time) {
        if (timeNow < time)
            revert();
        _;
    }

    /// Erase ownership information.
    /// May only be called 6 weeks after
    /// the contract has been created.
    /// @custom:key ensures \old(owner) == msg.sender && timeNow >= creationTime + 3628800 && owner == address(0)
    function disown()
        public
        onlyBy(owner)
        onlyAfter(creationTime + 6 weeks)
    {
        delete owner;
    }

    // This modifier requires a certain
    // fee being associated with a function call.
    // If the caller sent too much, he or she is
    // refunded, but only after the function body.
    // This was dangerous before Solidity version 0.4.0,
    // where it was possible to skip the part after `_;`.
    modifier costs(uint amount) {
        if (msg.value < amount)
            revert();

        _;
        if (msg.value > amount)
            payable(msg.sender).transfer(msg.value - amount);
    }

    /// @custom:key ensures msg.value >= 200000000000000000000 && owner == newOwner
    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) + 200000000000000000000
    function forceOwnerChange(address newOwner)
        public
        payable
        costs(200 ether)
    {
        owner = newOwner;
        // just some example condition
        if (uint160(owner) & 0 == 1)
            // This did not refund for Solidity
            // before version 0.4.0.
            return;
        // refund overpaid fees
    }
}
