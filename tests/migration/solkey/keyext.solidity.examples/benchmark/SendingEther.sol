// Source: https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/sending-ether/SendingEther.sol
// Changes: getBalance() is dropped (address(this).balance crashes the parser); the require
// messages are dropped; the unused `bytes memory data` of sendViaCall is not bound.
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract ReceiveEther {
    /*
    Which function is called, fallback() or receive()?

           send Ether
               |
         msg.data is empty?
              / \
            yes  no
            /     \
    receive() exists?  fallback()
         /   \
        yes   no
        /      \
    receive()   fallback()
    */

    // Function to receive Ether. msg.data must be empty
    receive() external payable {}

    // Fallback function is called when msg.data is not empty
    fallback() external payable {}
}

contract SendEther {
    /// @custom:key ensures _to != address(this) && _to != msg.sender -> net(_to) == \old(net(_to)) - msg.value && net(msg.sender) == \old(net(msg.sender)) + msg.value
    /// @custom:key ensures _to == msg.sender -> net(msg.sender) == \old(net(msg.sender))
    function sendViaTransfer(address payable _to) public payable {
        // This function is no longer recommended for sending Ether.
        _to.transfer(msg.value);
    }

    /// @custom:key ensures _to != address(this) && _to != msg.sender -> net(_to) == \old(net(_to)) - msg.value && net(msg.sender) == \old(net(msg.sender)) + msg.value
    /// @custom:key ensures _to == msg.sender -> net(msg.sender) == \old(net(msg.sender))
    function sendViaSend(address payable _to) public payable {
        // Send returns a boolean value indicating success or failure.
        // This function is not recommended for sending Ether.
        bool sent = _to.send(msg.value);
        require(sent);
    }

    /// @custom:key ensures _to != address(this) && _to != msg.sender -> net(_to) == \old(net(_to)) - msg.value && net(msg.sender) == \old(net(msg.sender)) + msg.value
    /// @custom:key ensures _to == msg.sender -> net(msg.sender) == \old(net(msg.sender))
    function sendViaCall(address payable _to) public payable {
        // Call returns a boolean value indicating success or failure.
        // This is the current recommended method to use.
        (bool sent,) = _to.call{value: msg.value}("");
        require(sent);
    }
}
