// Source: https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/app/erc20/ERC20.sol
// Changes: the import of IERC20 is inlined (from IERC20.sol of the same commit); events and
// emits are dropped; `returns (bool)` becomes `returns (bool success)`, since `\result` needs a
// named return.
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

interface IERC20 {
    function totalSupply() external view returns (uint256);
    function balanceOf(address account) external view returns (uint256);
    function transfer(address recipient, uint256 amount)
        external
        returns (bool);
    function allowance(address owner, address spender)
        external
        view
        returns (uint256);
    function approve(address spender, uint256 amount) external returns (bool);
    function transferFrom(address sender, address recipient, uint256 amount)
        external
        returns (bool);
}

contract ERC20 is IERC20 {
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    string public name;
    string public symbol;
    uint8 public decimals;

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
    function transfer(address recipient, uint256 amount)
        external
        returns (bool success)
    {
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

    function _mint(address to, uint256 amount) internal {
        balanceOf[to] += amount;
        totalSupply += amount;
    }

    function _burn(address from, uint256 amount) internal {
        balanceOf[from] -= amount;
        totalSupply -= amount;
    }

    /// @custom:key requires amount >= 0
    /// @custom:key ensures balanceOf[to] == \old(balanceOf[to]) + amount && totalSupply == \old(totalSupply) + amount
    function mint(address to, uint256 amount) external {
        _mint(to, amount);
    }

    /// @custom:key requires amount >= 0 && balanceOf[from] >= amount && totalSupply >= amount
    /// @custom:key ensures balanceOf[from] == \old(balanceOf[from]) - amount && totalSupply == \old(totalSupply) - amount
    function burn(address from, uint256 amount) external {
        _burn(from, amount);
    }
}
