// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.4;

// The `this`-based twins of tests/solc/open/SolcPaymentsOpen.sol's self-calls:
// a `try this.f()` runs `f`'s body in a frame of its own (`docs/options.md`
// O7), so these hold wherever the contract is deployed, with no premise on
// its address.  A callee is run only if it is declared before its caller.
contract SelfCalls {
    int ix;

    /// @custom:key skip
    function gOne(bool b) external pure returns (uint) {
        require(b);
        return 13;
    }

    /// @custom:key skip
    function setIx() external {
        ix = 42;
    }

    /// @custom:key skip
    function getIx() external view returns (int) {
        return ix;
    }

    /// @custom:key skip
    function noop() external pure {
    }

    // pending: each `catch` block is a goal from the caller's state, the
    // callee not known to end normally (`docs/options.md` O7)
    /// solc: semanticTests/tryCatch/simple_notuple.sol
    /// @custom:key box
    function tryCatchExactReturn(uint q) public view {
        require(q == 1);
        bool flag = q == 1;
        uint r = 0;
        try this.gOne(flag) returns (uint a) {
            r = a;
        } catch {
            r = 9;
        }
        assert(r == 13);
    }

    // the value bound by the success block is the callee's: its own goal
    // reads it (the catch-all's goal is the caller's, as for any `try`)
    /// solc: semanticTests/tryCatch/simple_notuple.sol
    /// @custom:key box
    function tryReturnInSuccess(uint q) public view {
        require(q == 1);
        bool flag = q == 1;
        try this.gOne(flag) returns (uint a) {
            assert(a == 13);
        } catch {
        }
    }

    /// solc: smtCheckerTests/try_catch/try_2.sol
    /// @custom:key box
    function trySuccessRunsCallee() public {
        ix = 0;
        try this.setIx() {
            int r = ix;
            assert(r == 42);
        } catch (bytes memory) {
            int r = ix;
            assert(r == 0);
        }
    }

    /// solc: smtCheckerTests/try_catch/try_multiple_catch_clauses.sol
    /// @custom:key box
    function tryMultipleCatchClausesSuccess() public {
        ix = 1;
        bool success = false;
        try this.setIx() {
            success = true;
            int r = ix;
            assert(r == 42);
        } catch Error(string memory) {
        } catch (bytes memory) {
        }
        int s = ix;
        assert((success && s == 42) || (!success && s == 1));
    }

    /// solc: smtCheckerTests/try_catch/try_nested_1.sol
    /// @custom:key box
    function tryNestedGetter() public view {
        int y2 = 42;
        bool success = false;
        try this.getIx() returns (int v) {
            y2 = v;
            try this.getIx() returns (int w) {
                success = true;
                y2 = w;
            } catch {}
        } catch {}
        int cur = ix;
        assert(!success || y2 == cur);
    }

    /// solc: semanticTests/revertStrings/called_contract_has_code.sol
    /// @custom:key box
    function callWithoutCodeReverts() public {
        SelfCalls(payable(address(0))).noop();
        assert(false);
    }
}
