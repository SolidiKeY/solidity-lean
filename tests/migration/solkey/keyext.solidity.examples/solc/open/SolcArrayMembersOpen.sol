// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SolcArrayMembersOpen {
    uint[] popIso;

    // open: the bare member access popIso.pop; as a statement is stuck on the program text
    /// solc: semanticTests/array/pop/array_pop_isolated.sol
    function popIsolated() public view {
        uint x = 2;
        popIso.pop;
        x = 3;
        assert(x == 3);
    }

}
