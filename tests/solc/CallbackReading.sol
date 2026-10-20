// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// A plain obligation whose callee may write the state is read with
// callbacks (`ValidT .noCallback`, docs/options.md O7): the callee may be
// this contract.
contract CallbackReading {
    int ix;
    function setIx() external { ix = 42; }
    function getIx() external view returns (int) { return ix; }

    /// @custom:key box
    function localKept(address p) public {
        int a = 1;
        try CallbackReading(p).setIx() { a = a + 1; } catch { }
        assert(a >= 1);
    }

    /// @custom:key box
    function storageLost(address p) public {
        ix = 0;
        try CallbackReading(p).setIx() { } catch { }
        assert(ix == 0);
    }

    /// @custom:key box
    function staticKept(address p) public {
        ix = 0;
        try CallbackReading(p).getIx() returns (int) { } catch { }
        assert(ix == 0);
    }

    /// @custom:key box
    function valueCallLost(address p) public {
        ix = 0;
        (bool ok, ) = payable(p).call{value: 0}("");
        assert(ix == 0);
    }
}
