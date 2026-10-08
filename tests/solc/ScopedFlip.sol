// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// One box function, for the scoped flip's switches
// (`Solidity/Solkey/ScopedFlip.lean`): `solc_problems … legacy`,
// `solc_scoped_problems … main decl` and the scoped `#solkey_derive?`.
contract ScopedFlip {
    uint age;

    /// @custom:key box
    function additionStorageWrite(uint x, uint y) public {
        require(x == 5 && y == 7);
        age = x + y;
        uint r = age;
        assert(r == 12);
    }
}
