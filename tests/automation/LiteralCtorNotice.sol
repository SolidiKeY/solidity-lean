// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// AU03 diagnostic fixture: no function row can report this constructor loop.
contract LiteralCtorNotice {
    uint value;
    constructor() {
        uint i = 0;
        while (i < 2) { i++; }
        value = i;
    }
}
