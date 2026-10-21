// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.4;

// Revert data reaching a `catch` (docs/semantic-gaps.md, "Revert data"): a
// self-call's `require(c, "m")` / `revert("m")` reason is decoded into
// `catch Error(string memory r)`, and `catch (bytes memory d)` binds the raw
// data.  Only a callee declared before its caller is run (docs/options.md O8).
// The callees are `pure`: a callee that may write the state puts the obligation
// in the callback reading (O7), whose leaves do not close a memory array's
// length yet.
contract RevertData {
    uint last;

    error E(uint256 code);
    error F();

    /// @custom:key skip
    function boom() external pure {
        require(false, "boom");
    }

    /// @custom:key skip
    function check(uint x) external pure {
        if (x > 3) {
            revert("big");
        }
    }

    /// @custom:key skip
    function plain(uint x) external pure {
        require(x > 3);
    }

    // the reason of `require(false, "boom")`, its bytes
    /// @custom:key box
    function reasonBytes() public view {
        try this.boom() {
        } catch Error(string memory r) {
            bytes memory b = bytes(r);
            assert(b.length == 4);
            assert(b[0] == bytes1(0x62));
            assert(b[3] == bytes1(0x6d));
        } catch {
        }
    }

    // `revert("big")` in a branch of the callee
    /// @custom:key box
    function reasonOfBranch() public {
        try this.check(5) {
        } catch Error(string memory r) {
            assert(bytes(r).length == 3);
            last = 1;
        } catch {
        }
    }

    // a revert with no reason: the raw data is empty
    /// @custom:key box
    function emptyData() public view {
        try this.plain(1) {
        } catch (bytes memory d) {
            assert(d.length == 0);
        }
    }

    /// @custom:key skip
    function failE() external pure {
        revert E(7);
    }

    /// @custom:key skip
    function failIf(uint x) external pure {
        require(x > 3, E(x));
    }

    /// @custom:key skip
    function failF() external pure {
        revert F();
    }

    // a custom error's data: its selector, `F()`'s 0x28811f59, folded as
    // solc folds it
    /// @custom:key box
    function customSelector() public view {
        try this.failF() {
        } catch (bytes memory d) {
            assert(d.length == 0 || d.length == 4 && d[0] == bytes1(0x28) && d[3] == bytes1(0x59));
        }
    }

    // a custom error's data: its selector (`E(uint256)`'s, 0x002ff067), then
    // its argument's word
    /// @custom:key box
    function customData() public view {
        try this.failE() {
        } catch (bytes memory d) {
            assert(d.length == 0 || d[3] == bytes1(0x67) && d[35] == bytes1(0x07));
        }
    }
}
