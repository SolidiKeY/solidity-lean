// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
// keccak256, the ABI and string-keyed mappings (docs/semantic-gaps.md,
// "Hashing and the ABI"): keccak256 an uninterpreted function of the bytes,
// abi.encode/encodePacked fresh memory bytes of solc's layout, abi.decode its
// inverse, a mapping(string => V) keyed by the hash.

contract Hashing {
    mapping(string => uint) ids;

    // one string hashed twice: the hash is a function (under the box: the
    // closer does not show a locally built string's hash returns)
    /// @custom:key box
    function equalStringsHashEqual() public pure {
        string memory s = "ab";
        assert(keccak256(bytes(s)) == keccak256(bytes(s)));
    }
    function hashParameter(bytes memory b) public pure {
        assert(keccak256(b) == keccak256(b));
    }
    function encodeLayout() public pure {
        bytes memory e = abi.encode(uint(258), true, address(0x1234));
        assert(e.length == 96 && e[30] == 0x01 && e[31] == 0x02 && e[63] == 0x01 &&
            e[94] == 0x12 && e[95] == 0x34);
    }
    function encodePacked() public pure {
        bytes memory e = abi.encodePacked(uint16(258), true, bytes2("ab"));
        assert(e.length == 5 && e[0] == 0x01 && e[1] == 0x02 && e[2] == 0x01 && e[3] == "a");
    }
    function decodeRoundtrip() public pure {
        bytes memory e = abi.encode(uint8(5), true);
        (uint8 a, bool c) = abi.decode(e, (uint8, bool));
        assert(a == 5 && c);
    }
    function stringKey(string memory k) public {
        ids[k] = 7;
        assert(ids[k] == 7);
    }
    function concatLengths() public pure {
        string memory s = string.concat("ab", "cde");
        bytes memory t = bytes.concat("x", "yz");
        assert(bytes(s).length == 5 && t.length == 3);
    }
}
