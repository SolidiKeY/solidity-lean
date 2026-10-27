// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.34;

contract CloudIntegrationBase {
    function inherited() public pure returns (uint) { return 7; }
}

contract CloudIntegration is CloudIntegrationBase {
    enum Plain { A, B }
    enum Packed { A, B }
    struct Cell { Packed value; }

    function plainInline() public pure returns (uint) {
        Plain[2] memory values = [Plain.A, Plain.B];
        return uint(values[1]);
    }

    function packedInline() public pure returns (uint) {
        Packed[2] memory values = [Packed.A, Packed.B];
        Cell memory cell = Cell(values[1]);
        return uint(cell.value);
    }
}
