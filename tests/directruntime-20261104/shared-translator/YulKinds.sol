// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
contract YulKinds {
    function shapes(uint256 x) public pure returns (uint256 result) {
        assembly {
            function helper(a) -> out {
                if iszero(a) { out := 0 leave }
                out := add(a, 1)
            }
            let sum := 0
            for { let i := 0 } lt(i, x) { i := add(i, 1) } {
                if eq(i, 2) { continue }
                if gt(i, 4) { break }
                sum := add(sum, i)
            }
            switch x
            case 0 { result := helper(sum) }
            default { result := helper(x) }
            pop(sum)
        }
    }
}
