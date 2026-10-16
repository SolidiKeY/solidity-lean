// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

// Source: https://github.com/Cyfrin/solidity-by-example.github.io/blob/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/enum/Enum.sol
// Changes: comments dropped; get's return value is named s.
contract Enum {
    enum Status {
        Pending,
        Shipped,
        Accepted,
        Rejected,
        Canceled
    }

    Status public status;

    /// @custom:key ensures \result == status && status == \old(status)
    function get() public view returns (Status s) {
        return status;
    }

    /// @custom:key ensures status == _status
    function set(Status _status) public {
        status = _status;
    }

    /// @custom:key ensures status == Status.Canceled
    function cancel() public {
        status = Status.Canceled;
    }

    /// @custom:key ensures status == Status.Pending
    function reset() public {
        delete status;
    }
}
