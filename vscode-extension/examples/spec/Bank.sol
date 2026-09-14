// SPDX-License-Identifier: MIT
pragma solidity 0.8.33;

/// A two-account ledger, specified in SolSpec.
///
/// The contract invariant is assumed on entry to every function and
/// proved on exit; it is what makes `balTo += amount` provably free of
/// overflow.
///
/// @custom:invariant balSender + balTo <= 115792089237316195423570985008687907853269984665640564039457584007913129639935
contract Bank {
    uint256 balSender;
    uint256 balTo;

    /// Move `amount` from the sender to the recipient.
    ///
    /// @custom:requires amount <= balSender
    /// @custom:ensures balSender == old(balSender) - amount
    /// @custom:ensures balTo == old(balTo) + amount
    /// @custom:ensures balSender + balTo == old(balSender) + old(balTo)
    /// @custom:modifies balSender, balTo
    function transfer(uint256 amount) public {
        balSender -= amount;
        balTo += amount;
    }

    /// The same transfer without a precondition: under the box reading a
    /// revert discharges the obligation, so the `require` carries it.
    ///
    /// @custom:partial
    /// @custom:ensures balSender == old(balSender) - amount
    /// @custom:reverts_when amount > balSender
    /// @custom:modifies balSender, balTo
    function guardedTransfer(uint256 amount) public {
        require(amount <= balSender);
        balSender -= amount;
        balTo += amount;
    }

    /// A read-only query, with a ghost assertion in the middle.
    ///
    /// @custom:requires balSender >= 1
    /// @custom:ensures result == balSender
    /// @custom:modifies
    function senderBalance() public view returns (uint256 result) {
        uint256 snapshot = balSender;
        /// @custom:assert snapshot >= 1
        result = snapshot;
    }
}
