// SPDX-License-Identifier: MIT
pragma solidity >=0.8.0;
contract PaymentInvalidCallee {
    fallback() external payable {}
    function invalid(bool c) public {
        (c ? payable(this).transfer : payable(this).transfer)(0);
    }
}
