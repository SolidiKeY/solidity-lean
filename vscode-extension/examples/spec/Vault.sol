// SPDX-License-Identifier: MIT
pragma solidity 0.8.33;

/// Exercises the parts of the language beyond plain scalars: mappings,
/// arrays, structs, branches, quantifiers and ghost steps.
contract Vault {
    struct Account {
        uint256 balance;
        bool frozen;
    }

    mapping(uint256 => uint256) balances;
    uint256[] log;
    Account owner;
    uint256 total;

    /// A mapping write, read back at the same key.
    ///
    /// @custom:requires !owner.frozen
    /// @custom:ensures balances[who] == amount
    /// @custom:modifies balances
    function credit(uint256 who, uint256 amount) public {
        balances[who] = amount;
    }

    /// Branching on a symbolic condition: `sol_spec` splits the `if`
    /// and both branches have to establish the postcondition.
    ///
    /// @custom:requires total <= 1000
    /// @custom:ensures total <= 1001
    /// @custom:modifies total
    function bump(bool go) public {
        if (go) {
            total += 1;
        } else {
            total = 0;
        }
    }

    /// A struct field, and a ghost assertion between the two writes.
    ///
    /// @custom:ensures owner.balance == amount
    /// @custom:ensures owner.frozen
    /// @custom:modifies owner
    function seize(uint256 amount) public {
        owner.balance = amount;
        /// @custom:assert owner.balance == amount
        owner.frozen = true;
    }

    /// `push` extends the log; the length grows by one. A quantifier
    /// over the old part of the log shows the bounded-forall syntax.
    ///
    /// @custom:requires forall i in 0 .. log.length :: log[i] <= total
    /// @custom:ensures log.length == old(log.length) + 1
    /// @custom:modifies log
    function record(uint256 entry) public {
        log.push(entry);
    }

    /// Outside the fragment: reported, not silently skipped.
    ///
    /// @custom:ensures total == 0
    function loopy(uint256 n) public {
        for (uint256 i = 0; i < n; i++) {
            total = 0;
        }
    }
}
