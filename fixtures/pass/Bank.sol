// SPDX-License-Identifier: MIT
pragma solidity 0.8.33;

// The Scalar.lean `transfer` example as source. The conservation invariant
// `balSender + balTo <= 2^256-1` is a contract invariant the slice cannot state, so the fixture
// assumes it with a leading require — phrased via checked subtraction (which cannot panic, since
// balSender is in range) rather than `balSender + balTo` (which could).
contract Bank {
    uint256 balSender;
    uint256 balTo;

    function transfer(uint256 amount) public {
        require(balTo <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 - balSender);
        require(amount <= balSender);
        balSender -= amount;
        balTo += amount;
    }
}
