// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity >=0.8.0;

// Source: https://github.com/transmissions11/solmate/blob/v7/src/auth/Owned.sol
// Changes: made concrete; comments, the event and the require message dropped. setOwner has no
// requires on the caller: its ensures proves that only the owner can change the owner.
contract SolmateOwned {
    address public owner;

    modifier onlyOwner() virtual {
        require(msg.sender == owner);

        _;
    }

    /// @custom:key ensures owner == _owner
    constructor(address _owner) {
        owner = _owner;
    }

    /// @custom:key ensures \old(owner) == msg.sender && owner == newOwner
    function setOwner(address newOwner) public virtual onlyOwner {
        owner = newOwner;
    }
}
