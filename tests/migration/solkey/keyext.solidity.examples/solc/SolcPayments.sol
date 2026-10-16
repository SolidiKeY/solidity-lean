// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.4;

/// Ports of semanticTests/{payable,receive,fallback,reverts,errors,tryCatch} and
/// smtCheckerTests/{special,blockchain_state,functions,try_catch}.
contract SolcPayments {
    struct S {
        uint value;
        address origin;
        uint number;
    }

    struct error {
        uint error;
    }

    address payable recipient;
    address sender;
    uint value;
    uint counter;
    uint x;
    uint y;
    uint fx;
    uint fy;
    int ix;
    error _struct;

    receive() external payable {
        receiveBody();
    }

    fallback() external payable {
        fallbackBody();
    }

    /// @custom:key skip
    function g(bool b) external pure returns (uint, uint) {
        require(b);
        return (1, 2);
    }

    /// @custom:key skip
    function gOne(bool b) external pure returns (uint) {
        require(b);
        return 13;
    }

    /// @custom:key skip
    function gRequire(bool b) external pure {
        require(b);
    }

    /// @custom:key skip
    function gAssert(bool b) external pure {
        assert(b);
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
    function setBelow(int n) external {
        require(n < 100);
        ix = n;
    }

    /// @custom:key skip
    function noop() external pure {
    }

    /// @custom:key skip
    function pair() external pure returns (uint, uint) {
    }

    /// @custom:key skip
    function shadowing() external returns (uint, bool) {
    }

    /// solc: smtCheckerTests/special/msg_sender_1.sol
    function msgSenderTwice() public view {
        address a = msg.sender;
        address b = msg.sender;
        assert(a == b);
    }

    /// solc: smtCheckerTests/special/msg_sender_2.sol
    /// @custom:key box
    function msgSenderNonZero() public view {
        require(msg.sender != address(0));
        address a = msg.sender;
        address b = msg.sender;
        assert(a == b);
    }

    function checkMsgVars() internal view {
        uint v = value;
        assert(v >= 0);
        address s = sender;
        assert(s == msg.sender);
        assert(v == msg.value);
    }

    /// solc: smtCheckerTests/special/msg_vars_chc_internal.sol
    /// @custom:key box
    function msgVarsInternal() public payable {
        sender = msg.sender;
        value = msg.value;
        uint v = value;
        require(v == 42);
        checkMsgVars();
    }

    /// solc: smtCheckerTests/special/ether_units.sol
    function etherUnits() public pure {
        assert(1000000000000000000 wei == 1 ether);
        assert(1000000000 wei == 1 gwei);
        assert(1000000000 gwei == 1 ether);
    }

    /// solc: smtCheckerTests/special/time_units.sol
    function timeUnits() public pure {
        assert(1 == 1 seconds);
        assert(2 minutes == 120 seconds);
        assert(2 hours == 120 minutes);
        assert(2 days == 48 hours);
        assert(2 weeks == 14 days);
    }

    /// solc: smtCheckerTests/special/shadowing_1.sol
    function shadowBuiltins() public payable {
        S memory msg;
        msg.value = 42;
        msg.number = 666;
        S memory tx;
        tx.value = 42;
        tx.number = 666;
        S memory block;
        block.value = 42;
        block.number = 666;
        uint v = msg.value;
        address o = tx.origin;
        uint n = block.number;
        assert(v == 42);
        assert(o == address(0));
        assert(n == 666);
    }

    function requireNoValue() internal view {
        require(msg.value == 0);
    }

    function assertNoValue() internal view {
        assert(msg.value == 0);
    }

    /// solc: smtCheckerTests/functions/payable_2.sol
    /// @custom:key box
    function payableRequireThenAssert() public view {
        requireNoValue();
        assertNoValue();
        assertNoValue();
    }

    modifier tryCircumvent() {
        if (false) _;
    }

    function msgvalue() internal view returns (uint) {
        return msg.value;
    }

    function circumvented() internal view tryCircumvent returns (uint) {
        return msgvalue();
    }

    /// solc: semanticTests/payable/no_nonpayable_circumvention_by_modifier.sol
    function noCircumventionByModifier() public view {
        uint r = circumvented();
        assert(r == 0);
    }

    /// solc: smtCheckerTests/blockchain_state/transfer_4.sol
    /// @custom:key box
    function transferAfterPayment() public payable {
        require(msg.value > 1);
        address payable r = recipient;
        r.transfer(1);
    }

    /// solc: semanticTests/reverts/assert_require.sol
    /// @custom:key box
    function assertValTrue(uint p) public pure {
        require(p == 1);
        bool val = p == 1;
        assert(val == true);
    }

    /// solc: semanticTests/reverts/assert_require.sol
    function requireValTrue() public pure {
        bool val = true;
        require(val);
        bool r = true;
        assert(r);
    }

    /// solc: semanticTests/reverts/simple_throw.sol
    function simpleThrowTaken() public pure {
        uint p = 11;
        uint r;
        if (p > 10) r = p + 10;
        else revert();
        assert(r == 21);
    }

    /// solc: semanticTests/reverts/simple_throw.sol
    /// @custom:key box
    function simpleThrowReverts(uint p) public pure {
        require(p == 1);
        uint r;
        if (p > 10) r = p + 10;
        else revert();
        assert(false);
    }

    /// solc: semanticTests/reverts/revert.sol
    /// @custom:key box
    function revertAfterWrite() public {
        x = 1;
        revert();
        assert(false);
    }

    /// solc: semanticTests/reverts/error_struct.sol
    function errorStruct() public {
        uint p = 7;
        _struct.error = p;
        uint r = _struct.error;
        assert(r == 7);
    }

    function countCond(bool condition) internal returns (bool) {
        counter++;
        return condition;
    }

    /// solc: semanticTests/errors/require_error_condition_evaluated_only_once.sol
    function conditionEvaluatedOnce() public {
        counter = 0;
        require(countCond(true));
        uint r = counter;
        assert(r == 1);
    }

    function setY(bool c) internal returns (bool) {
        y = 42;
        return c;
    }

    /// solc: semanticTests/errors/require_error_evaluation_order_2.sol
    function evaluationOrder() public {
        require(setY(true));
        uint r = y;
        assert(r == 42);
    }

    /// solc: semanticTests/errors/require_error_function_join_control_flow.sol
    function joinControlFlow() public {
        bool c = true;
        x = 0;
        y = 42;
        uint z = x;
        if (y == 42) {
            x = 21;
        } else {
            require(c);
        }
        y /= 2;
        uint rx = x;
        uint ry = y;
        assert(rx == 21 && ry == 21 && z == 0);
    }

    /// solc: semanticTests/errors/require_error_function_join_control_flow.sol
    /// @custom:key box
    function joinControlFlowSecondCallReverts() public {
        bool c = false;
        x = 21;
        y = 21;
        if (y == 42) {
            x = 21;
        } else {
            require(c);
        }
        assert(false);
    }

    /// solc: semanticTests/tryCatch/simple.sol
    /// @custom:key box
    function tryCatchSimple(address p, uint q) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef && q == 1);
        bool flag = q == 1;
        try SolcPayments(payable(p)).g(flag) returns (uint a, uint b) {
            x = a;
            y = b;
            uint rx = x;
            uint ry = y;
            assert(rx == a && ry == b);
        } catch {
            x = 9;
            y = 10;
            uint rx = x;
            uint ry = y;
            assert(rx == 9 && ry == 10);
        }
    }

    /// solc: semanticTests/tryCatch/simple_notuple.sol
    /// @custom:key box
    function tryCatchNotuple(address p, uint q) public pure {
        require(p == 0x00000000000000000000000000000000DeaDBeef && q == 1);
        bool flag = q == 1;
        uint r = 0;
        try SolcPayments(payable(p)).gOne(flag) returns (uint a) {
            r = a;
            assert(r == a);
        } catch {
            r = 9;
            assert(r == 9);
        }
    }

    /// solc: semanticTests/tryCatch/require.sol
    /// @custom:key box
    function tryCatchRequire(address p, uint q) public pure {
        require(p == 0x00000000000000000000000000000000DeaDBeef && q == 1);
        bool flag = q == 1;
        uint r = 0;
        try SolcPayments(payable(p)).gRequire(flag) {
            r = 1;
        } catch {
            r = 2;
        }
        assert(r == 1 || r == 2);
    }

    /// solc: semanticTests/tryCatch/assert.sol
    /// @custom:key box
    function tryCatchAssert(address p, uint q) public pure {
        require(p == 0x00000000000000000000000000000000DeaDBeef && q == 1);
        bool flag = q == 1;
        uint r = 0;
        try SolcPayments(payable(p)).gAssert(flag) {
            r = 1;
        } catch {
            r = 2;
        }
        assert(r == 1 || r == 2);
    }

    /// solc: semanticTests/tryCatch/structured.sol
    /// @custom:key box
    function tryCatchStructured(address p, uint q) public pure {
        require(p == 0x00000000000000000000000000000000DeaDBeef && q == 1);
        bool flag = q == 1;
        uint rx = 0;
        uint ry = 0;
        try SolcPayments(payable(p)).g(flag) returns (uint a, uint b) {
            rx = a;
            ry = b;
            assert(rx == a && ry == b);
        } catch Error(string memory) {
            assert(rx == 0 && ry == 0);
        }
    }

    /// solc: semanticTests/tryCatch/nested.sol
    /// @custom:key box
    function tryCatchNested(address p, uint q) public pure {
        require(p == 0x00000000000000000000000000000000DeaDBeef && q == 1);
        bool c1 = q == 1;
        bool c2 = q == 1;
        uint rx = 0;
        try SolcPayments(payable(p)).g(c1) returns (uint a, uint) {
            try SolcPayments(payable(p)).g(c2) returns (uint, uint) {
                rx = a;
                assert(rx == a);
            } catch Error(string memory) {
                rx = 12;
                assert(rx == 12);
            } catch (bytes memory) {
                rx = 13;
                assert(rx == 13);
            }
        } catch Error(string memory) {
            rx = 99;
            assert(rx == 99);
        } catch (bytes memory) {
            rx = 98;
            assert(rx == 98);
        }
    }

    /// solc: semanticTests/tryCatch/panic.sol
    /// @custom:key box
    function tryCatchPanic(address p, uint q) public pure {
        require(p == 0x00000000000000000000000000000000DeaDBeef && q == 1);
        bool flag = q == 1;
        uint r;
        uint code;
        try SolcPayments(payable(p)).uf(flag, 7, 6) returns (uint b) {
            r = b;
            assert(r == b && code == 0);
        } catch Panic(uint c) {
            code = c;
            assert(r == 0 && code == c);
        }
    }

    /// solc: smtCheckerTests/try_catch/try_1.sol
    /// @custom:key box
    function tryCatchKeepsState(address p) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        ix = 0;
        bool success = false;
        try SolcPayments(payable(p)).setIx() {
            success = true;
        } catch (bytes memory) {
            int r = ix;
            assert(r == 0);
        }
    }

    /// solc: smtCheckerTests/try_catch/try_4.sol
    /// @custom:key box
    function tryCatchRevertsChanges(address p) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        ix = 0;
        try SolcPayments(payable(p)).noop() {
        } catch {
            int r = ix;
            assert(r == 0);
        }
    }

    /// solc: smtCheckerTests/try_catch/try_5.sol
    /// @custom:key box
    function tryCatchBoundKept(address p) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        ix = 0;
        try SolcPayments(payable(p)).noop() {
            int r = ix;
            assert(r < 100);
        } catch {
            int r = ix;
            assert(r == 0);
        }
    }

    /// solc: smtCheckerTests/try_catch/try_multiple_catch_clauses.sol
    /// @custom:key box
    function tryMultipleCatchClausesCatch(address p) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        ix = 1;
        try SolcPayments(payable(p)).setIx() {
        } catch Error(string memory) {
            int r = ix;
            assert(r == 1);
        } catch (bytes memory) {
            int r = ix;
            assert(r == 1);
        }
    }

    /// solc: smtCheckerTests/try_catch/try_multiple_catch_clauses_2.sol
    /// @custom:key box
    function tryMultipleCatchClauses2(address p) public pure {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        uint r = 0;
        bool success = false;
        try SolcPayments(payable(p)).noop() {
            success = true;
            r = 1;
        } catch Error(string memory) {
            r = 2;
        } catch (bytes memory) {
            r = 3;
        }
        assert(r > 0 && r < 4);
    }

    /// solc: smtCheckerTests/try_catch/try_nested_2.sol
    /// @custom:key box
    function tryNested2(address p) public pure {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        uint choice = 42;
        try SolcPayments(payable(p)).pair() returns (uint, uint) {
            choice = 10;
            try SolcPayments(payable(p)).pair() returns (uint, uint) {
                choice = 1;
            } catch {
                choice = 2;
            }
        } catch {
            choice = 3;
        }
        assert(choice >= 1 && choice <= 3);
    }

    /// solc: smtCheckerTests/try_catch/try_multiple_returned_values.sol
    /// @custom:key box
    function tryReturnsShadowState(address p) public {
        require(p == 0x00000000000000000000000000000000DeaDBeef);
        ix = 0;
        try SolcPayments(payable(p)).shadowing() returns (uint ix, bool c) {
        } catch {
            int r = ix;
            assert(r == 0);
        }
    }

    function fallbackBody() internal {
        if (fx == 2) return;
        fx++;
    }

    function receiveBody() internal {
        ++fy;
    }

    function fallbackIncrement() internal {
        ++fx;
    }

    /// solc: semanticTests/fallback/falback_return.sol
    function fallbackReturn() public {
        fx = 0;
        fallbackBody();
        uint r1 = fx;
        fallbackBody();
        uint r2 = fx;
        fallbackBody();
        uint r3 = fx;
        fallbackBody();
        uint r4 = fx;
        assert(r1 == 1 && r2 == 2 && r3 == 2 && r4 == 2);
    }

    /// solc: semanticTests/fallback/fallback_or_receive.sol
    function fallbackOrReceive() public {
        fx = 0;
        fy = 0;
        receiveBody();
        uint a1 = fx;
        uint b1 = fy;
        receiveBody();
        uint b2 = fy;
        fallbackIncrement();
        uint a3 = fx;
        fallbackIncrement();
        uint a4 = fx;
        uint b4 = fy;
        assert(a1 == 0 && b1 == 1 && b2 == 2 && a3 == 1 && a4 == 2 && b4 == 2);
    }
}
