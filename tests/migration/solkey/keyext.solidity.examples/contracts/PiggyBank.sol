// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// @custom:key invariant state != PiggyBankState.Broken -> balance == net(owner)
/// @custom:key invariant state == PiggyBankState.Broken -> net(owner) == 0
contract PiggyBank {
    enum PiggyBankState { Unused, InUse, Broken }

    address payable public owner;
    PiggyBankState public state;
    uint public timeOfFirstDeposit;
    uint public balance;
    uint timeNow;

    constructor(address payable _owner) {
        owner = _owner;
        state = PiggyBankState.Unused;
        balance = 0;
    }

    /// @custom:key requires msg.sender == owner && state != PiggyBankState.Broken
    /// @custom:key requires state == PiggyBankState.Unused || state == PiggyBankState.InUse
    /// @custom:key ensures balance == net(owner) && state == PiggyBankState.InUse
    function addMoney() public payable {
        address own = owner;
        require(msg.sender == own);
        require(state != PiggyBankState.Broken);
        uint b = balance;
        uint tn = timeNow;
        balance = b + msg.value;
        if (state == PiggyBankState.Unused) {
            state = PiggyBankState.InUse;
            timeOfFirstDeposit = tn;
        }
    }

    /// @custom:key requires msg.sender == owner && state == PiggyBankState.InUse
    /// @custom:key requires timeNow >= timeOfFirstDeposit + 31536000
    /// @custom:key ensures net(owner) == 0 && state == PiggyBankState.Broken
    function breakPiggyBank() public {
        address own = owner;
        require(msg.sender == own);
        require(state == PiggyBankState.InUse);
        uint dl = timeOfFirstDeposit + 31536000;
        require(timeNow >= dl);
        uint b = balance;
        state = PiggyBankState.Broken;
        owner.transfer(b);
    }
}
