// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// Wrapped Ether, the canonical WETH9 (https://etherscan.io/address/0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2#code),
// ported from Solidity 0.4.18 to 0.8. Deviations: the 0.8 port turns the fallback into
// receive(), msg.sender.transfer into payable(msg.sender).transfer and uint(-1) into its
// literal value (type(uint).max is not supported); forced by the supported fragment, the events
// and the string name/symbol are dropped, totalSupply() (this.balance) is dropped, the return
// values are named, and functions are declared before the functions that call them.
// deposit and withdraw tie the token balance to the payment ledger: whatever enters or leaves
// balanceOf[msg.sender] is exactly the ether msg.sender paid in or got back.
contract WETH9 {
    uint8 public decimals = 18;

    mapping(address => uint) public balanceOf;
    mapping(address => mapping(address => uint)) public allowance;

    /// @custom:key ensures balanceOf[msg.sender] == \old(balanceOf[msg.sender]) + msg.value
    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) + msg.value
    function deposit() public payable {
        balanceOf[msg.sender] += msg.value;
    }

    receive() external payable {
        deposit();
    }

    /// @custom:key requires wad >= 0
    /// @custom:key ensures balanceOf[msg.sender] == \old(balanceOf[msg.sender]) - wad
    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) - wad
    function withdraw(uint wad) public {
        require(balanceOf[msg.sender] >= wad);
        balanceOf[msg.sender] -= wad;
        payable(msg.sender).transfer(wad);
    }

    /// @custom:key requires wad >= 0
    /// @custom:key ensures \result && allowance[msg.sender][guy] == wad
    function approve(address guy, uint wad) public returns (bool ok) {
        allowance[msg.sender][guy] = wad;
        return true;
    }

    // 115792089237316195423570985008687907853269984665640564039457584007913129639935 is
    // 2^256 - 1, the largest uint256: the original's uint(-1), type(uint).max in 0.8, which is
    // not supported yet. An allowance of that value is unlimited and never decreases.
    /// @custom:key requires wad >= 0
    /// @custom:key ensures \result
    /// @custom:key ensures src != dst -> balanceOf[src] == \old(balanceOf[src]) - wad && balanceOf[dst] == \old(balanceOf[dst]) + wad
    /// @custom:key ensures src == dst -> balanceOf[src] == \old(balanceOf[src])
    /// @custom:key ensures src != msg.sender && \old(allowance[src][msg.sender]) != 115792089237316195423570985008687907853269984665640564039457584007913129639935 -> allowance[src][msg.sender] == \old(allowance[src][msg.sender]) - wad
    function transferFrom(address src, address dst, uint wad) public returns (bool ok) {
        require(balanceOf[src] >= wad);
        if (src != msg.sender && allowance[src][msg.sender] != 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
            require(allowance[src][msg.sender] >= wad);
            allowance[src][msg.sender] -= wad;
        }
        balanceOf[src] -= wad;
        balanceOf[dst] += wad;
        return true;
    }

    /// @custom:key skip
    function transfer(address dst, uint wad) public returns (bool) {
        return transferFrom(msg.sender, dst, wad);
    }
}
