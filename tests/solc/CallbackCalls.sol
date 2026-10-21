// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// Calls and loops whose callee calls back, read with callbacks
// (`ValidT .noCallback`, docs/options.md O3 and O7): a value call's callee
// may be this contract.
contract CallbackCalls {
    uint pings;

    function payOne(address p, uint x) internal returns (uint) {
        (bool ok, ) = payable(p).call{value: 0}("");
        return x + 1;
    }

    // `uint y = f(x)`, `f` paying: the call inlined (`ProvesC.callVal`)
    /// @custom:key box
    function valueThroughCall(address p) public {
        uint y = payOne(p, 1);
        assert(y == 2);
    }

    // a loop of value calls by its invariant (`ProvesC.invBox`)
    /// @custom:key box
    function loopOfCalls(address p, uint n) public {
        uint i = 0;
        /// @custom:key invariant i <= n
        while (i < n) {
            (bool ok, ) = payable(p).call{value: 0}("");
            i = i + 1;
        }
        assert(i == n);
    }

    // the same, a value call through a function in the body
    /// @custom:key box
    function loopOfValueCalls(address p, uint n) public {
        uint i = 0;
        /// @custom:key invariant i <= n
        while (i < n) {
            i = payOne(p, i);
        }
        assert(i == n);
    }

    // open: the callee may write `pings`
    /// @custom:key box
    function storageLostThroughCall(address p) public {
        pings = 0;
        uint y = payOne(p, 1);
        assert(pings == 0);
    }

    // open: the frame havocs `pings` at every head
    /// @custom:key box
    function storageLostInLoop(address p, uint n) public {
        pings = 0;
        uint i = 0;
        /// @custom:key invariant i <= n
        while (i < n) {
            (bool ok, ) = payable(p).call{value: 0}("");
            i = i + 1;
        }
        assert(pings == 0);
    }
}
