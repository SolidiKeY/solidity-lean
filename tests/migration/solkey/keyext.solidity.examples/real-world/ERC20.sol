// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// The ERC20 token of Solidity by Example (https://solidity-by-example.org/app/erc20/).
// Deviations, all forced by the supported fragment: the IERC20 interface and the events are
// dropped; the return value is named success; mint and burn
// inline the bodies of _mint and _burn, since a call nested in a body is not expanded. Checked
// arithmetic is not modelled, so the requires state the case in which the EVM would not revert
// on underflow (balance and allowance cover the amount).
contract ERC20 {
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    string public name;
    string public symbol;
    uint8 public decimals;

    /// @custom:key skip
    constructor(string memory _name, string memory _symbol, uint8 _decimals) {
        name = _name;
        symbol = _symbol;
        decimals = _decimals;
    }

    /// @custom:key requires amount >= 0 && balanceOf[msg.sender] >= amount
    /// @custom:key ensures \result && totalSupply == \old(totalSupply)
    /// @custom:key ensures msg.sender != recipient -> balanceOf[msg.sender] == \old(balanceOf[msg.sender]) - amount && balanceOf[recipient] == \old(balanceOf[recipient]) + amount
    /// @custom:key ensures msg.sender == recipient -> balanceOf[msg.sender] == \old(balanceOf[msg.sender])
    /// @custom:key ensures \forall address a; a != msg.sender && a != recipient -> balanceOf[a] == \old(balanceOf[a])
    function transfer(address recipient, uint256 amount) external returns (bool success) {
        balanceOf[msg.sender] -= amount;
        balanceOf[recipient] += amount;
        return true;
    }

    /// @custom:key requires amount >= 0
    /// @custom:key ensures \result && allowance[msg.sender][spender] == amount
    function approve(address spender, uint256 amount) external returns (bool success) {
        allowance[msg.sender][spender] = amount;
        return true;
    }

    /// @custom:key requires amount >= 0 && allowance[sender][msg.sender] >= amount && balanceOf[sender] >= amount
    /// @custom:key ensures \result && totalSupply == \old(totalSupply)
    /// @custom:key ensures allowance[sender][msg.sender] == \old(allowance[sender][msg.sender]) - amount
    /// @custom:key ensures sender != recipient -> balanceOf[sender] == \old(balanceOf[sender]) - amount && balanceOf[recipient] == \old(balanceOf[recipient]) + amount
    /// @custom:key ensures sender == recipient -> balanceOf[sender] == \old(balanceOf[sender])
    function transferFrom(address sender, address recipient, uint256 amount)
        external
        returns (bool success)
    {
        allowance[sender][msg.sender] -= amount;
        balanceOf[sender] -= amount;
        balanceOf[recipient] += amount;
        return true;
    }

    /// @custom:key requires amount >= 0
    /// @custom:key ensures balanceOf[to] == \old(balanceOf[to]) + amount && totalSupply == \old(totalSupply) + amount
    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
        totalSupply += amount;
    }

    /// @custom:key requires amount >= 0 && balanceOf[from] >= amount && totalSupply >= amount
    /// @custom:key ensures balanceOf[from] == \old(balanceOf[from]) - amount && totalSupply == \old(totalSupply) - amount
    function burn(address from, uint256 amount) external {
        balanceOf[from] -= amount;
        totalSupply -= amount;
    }
}
