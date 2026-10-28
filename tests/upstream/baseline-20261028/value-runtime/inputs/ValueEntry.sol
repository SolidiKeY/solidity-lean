pragma solidity ^0.8.0;
contract ValueEntry {
    uint counter;
    uint seenValue;
    address seenSender;
    uint seenBalance;
    constructor() { counter = 3; }
    function nonpayableEntry() external { counter = 9; }
    function payableEntry() external payable {
        counter = 11;
        seenValue = msg.value;
        seenSender = msg.sender;
        seenBalance = address(this).balance;
    }
    function ordinary() public { counter += 1; }
    function helper() internal { counter += 1; }
    function internalCall() external payable {
        ordinary();
        helper();
        seenValue = msg.value;
        seenSender = msg.sender;
        seenBalance = address(this).balance;
    }
    function writeFail() external payable {
        counter = 99;
        seenValue = msg.value;
        assert(false);
    }
}
