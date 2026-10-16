// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.4;

contract SolcPaymentsOpen {
    uint x;
    uint y;
    uint fy;
    int ix;
    bool lock;

    receive() external payable {
        ++fy;
    }

    /// @custom:key skip
    function gOne(bool b) external pure returns (uint) {
        require(b);
        return 13;
    }

    /// @custom:key skip
    function uf(bool b, uint p, uint q) external pure returns (uint) {
        require(b);
        return p - q;
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
    function id(int v) external pure returns (int) {
        return v;
    }

    /// @custom:key skip
    function noop() external pure {
    }

    // open: msgSender is an unbounded int with no range assumption, so msg.sender >= 0 is not provable
    /// solc: smtCheckerTests/special/msg_sender_range.sol
    function msgSenderRange() public view {
        assert(msg.sender >= address(0));
    }

    // open: msgValue >= 0 is not assumed by a .sol obligation, so (5 + v + v) - (4 + v) > 0 is not provable
    /// solc: smtCheckerTests/special/msg_value_1.sol
    function msgValueArith() public payable {
        uint lhs = (5 + msg.value + msg.value) - (4 + msg.value);
        assert(lhs > 0);
    }

    // open: msgValue >= 0 is not assumed by a .sol obligation
    /// solc: smtCheckerTests/special/range_check.sol
    function msgValueRange() public payable {
        assert(msg.value >= 0);
    }

    function lockedNoValue() internal view {
        bool l = lock;
        require(l == false);
        assert(msg.value == 0);
    }

    // open: a non-payable function's obligation does not assume msg.value == 0
    /// solc: smtCheckerTests/special/msg_value_3.sol
    function msgValueNonPayable() public {
        lock = false;
        lockedNoValue();
        lock = true;
    }

    function requireNoValue() internal view {
        require(msg.value == 0);
    }

    // open: a non-payable function's obligation does not assume msg.value == 0, so the require may revert
    /// solc: smtCheckerTests/functions/payable_1.sol
    function nonPayableRequireHolds() public view {
        requireNoValue();
    }

    // open: the callee of a try is never executed, so its return value 13 is unconstrained
    /// solc: semanticTests/tryCatch/simple_notuple.sol
    /// @custom:key box
    function tryCatchExactReturn(address p, uint q) public pure {
        require(p == 0x00000000000000000000000000000000DeaDBeef && q == 1);
        bool flag = q == 1;
        uint r = 0;
        try SolcPaymentsOpen(payable(p)).gOne(flag) returns (uint a) {
            r = a;
        } catch {
            r = 9;
        }
        assert(r == 13);
    }

    // open: the callee of a try is never executed, so its write x = 42 is not seen on success
    /// solc: smtCheckerTests/try_catch/try_2.sol
    /// @custom:key box
    function trySuccessRunsCallee(address p) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        ix = 0;
        try SolcPaymentsOpen(payable(p)).setIx() {
            int r = ix;
            assert(r == 42);
        } catch (bytes memory) {
            int r = ix;
            assert(r == 0);
        }
    }

    // open: closes in KeY but fails on the EVM: under noCallback a successful try keeps the caller's storage, though the callee here is the contract itself and sets ix = 42
    /// solc: smtCheckerTests/try_catch/try_2.sol
    /// @custom:key box
    function trySuccessKeepsStorageUnsound(address p) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        ix = 0;
        try SolcPaymentsOpen(payable(p)).setIx() {
            int r = ix;
            assert(r == 0);
        } catch (bytes memory) {
        }
    }

    // open: the callee of a try is never executed, so its write x = 42 is not seen on success
    /// solc: smtCheckerTests/try_catch/try_multiple_catch_clauses.sol
    /// @custom:key box
    function tryMultipleCatchClausesSuccess(address p) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        ix = 1;
        bool success = false;
        try SolcPaymentsOpen(payable(p)).setIx() {
            success = true;
            int r = ix;
            assert(r == 42);
        } catch Error(string memory) {
        } catch (bytes memory) {
        }
        int s = ix;
        assert((success && s == 42) || (!success && s == 1));
    }

    // open: the callee of a try is never executed, so the getter's result is not linked to ix
    /// solc: smtCheckerTests/try_catch/try_nested_1.sol
    /// @custom:key box
    function tryNestedGetter(address p) public view {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        int y2 = 42;
        bool success = false;
        try SolcPaymentsOpen(payable(p)).getIx() returns (int v) {
            y2 = v;
            try SolcPaymentsOpen(payable(p)).getIx() returns (int w) {
                success = true;
                y2 = w;
            } catch {}
        } catch {}
        int cur = ix;
        assert(!success || y2 == cur);
    }

    function postinc() internal returns (int) {
        ix += 1;
        return ix;
    }

    // open: no rule captures a try call argument with a side effect, so symbolic execution stops at the try
    /// solc: smtCheckerTests/try_catch/try_3.sol
    /// @custom:key box
    function tryArgumentSideEffect(address p) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        ix = 0;
        try SolcPaymentsOpen(payable(p)).id(postinc()) {
            int r = ix;
            assert(r == 1);
        } catch (bytes memory) {
        }
    }

    // open: an external call outside try has no rule, so symbolic execution stops at it
    /// solc: semanticTests/revertStrings/called_contract_has_code.sol
    /// @custom:key box
    function callWithoutCodeReverts() public {
        SolcPaymentsOpen(payable(address(0))).noop();
        assert(false);
    }

    // open: under noCallback a call keeps the caller's storage, so the receive increment is not seen
    /// solc: semanticTests/receive/empty_calldata_calls_receive.sol
    /// @custom:key box
    function callRunsReceive(address p) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        fy = 0;
        (bool ok, ) = payable(p).call{value: 0}("");
        uint r = fy;
        assert(ok && r == 1);
    }

    // open: closes in KeY but fails on the EVM: under noCallback a call keeps the caller's storage, though the empty-calldata call to the contract itself runs receive
    /// solc: semanticTests/receive/empty_calldata_calls_receive.sol
    /// @custom:key box
    function callKeepsStorageUnsound(address p) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        fy = 0;
        (bool ok, ) = payable(p).call{value: 0}("");
        uint r = fy;
        assert(r == 0);
    }
}
