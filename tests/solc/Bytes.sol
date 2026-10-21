// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
// bytesN, bytes and string: a bytesN is a uint of 8N bits holding its bytes
// big-endian, bytes and string a bytes1[] (docs/semantic-gaps.md, "Bytes and
// strings").

contract Bytes {
    bytes4 tag;
    bytes32 root;
    mapping(bytes32 => uint) votes;
    bytes data;
    string name;
    // a struct with byte members: the contract's own, spelling them
    struct Rec { bytes32 h; bytes2 tag; bytes b; string label; }
    Rec rec;
    mapping(string => Rec) recs;

    function literals() public pure {
        bytes2 a = "a";
        bytes2 b = "ab";
        bytes2 c = hex"6162";
        assert(a == 0x6100 && b == c && uint16(b) == 24930);
    }
    function compareAndIndex() public pure {
        bytes2 b = "ab";
        assert(b < "b" && b[0] == "a" && b[1] == 0x62 && b.length == 2);
    }
    /// @custom:key box
    function indexOutOfRange(uint i) public pure {
        require(i >= 4);
        bytes4 b = "abcd";
        bytes1 x = b[i];
        assert(false);
    }
    function conversions() public pure {
        bytes2 b = "ab";
        bytes1 s = bytes1(b);
        bytes4 w = bytes4(b);
        bytes4 v = b;
        assert(s == "a" && w == 0x61620000 && v == w && bytes2(uint16(b)) == b);
    }
    function bitwise() public pure {
        bytes1 a = 0x0f;
        bytes2 b = "ab";
        assert(~a == 0xf0 && (b << 8) == 0x6200 && (b & 0xff00) == 0x6100);
    }
    function stateAndKeys(bytes32 k) public {
        tag = "abcd";
        votes[k] = 1;
        votes["x"] = 2;
        assert(tag[3] == "d" && votes[k] == (k == "x" ? 2 : 1));
    }
    function parameter(bytes4 x) public pure {
        assert(uint32(x) < 2 ** 32);
    }
    function memoryBytes() public pure {
        bytes memory b = "abc";
        b[0] = "A";
        assert(b.length == 3 && b[0] == 0x41 && b[2] == "c");
    }
    function stringToBytes() public pure {
        string memory s = "hi";
        bytes memory b = bytes(s);
        assert(b.length == 2 && b[1] == "i");
    }
    function storagePushPop() public {
        data = "ab";
        data.push("c");
        assert(data.length == 3 && data[2] == "c");
        data.pop();
        assert(data.length == 2);
    }
    function storageString() public {
        name = "xy";
        assert(bytes(name).length == 2 && bytes(name)[1] == "y");
        delete name;
        assert(bytes(name).length == 0);
    }
    function memoryParameter(bytes memory m) public pure {
        if (m.length > 0) assert(uint8(m[0]) <= 255);
    }
    // byte types as struct members: read and written as locals of their types
    function structMembers() public {
        rec.tag = "ab";
        rec.h = "z";
        assert(rec.tag[1] == "b" && rec.tag.length == 2 && rec.h[0] == "z");
        rec.label = "hi";
        assert(bytes(rec.label).length == 2);
    }
    function structMemberBytes() public {
        rec.b = "a";
        rec.b.push("x");
        assert(rec.b.length == 2 && rec.b[1] == "x");
    }
    function memoryStructLiteral() public pure {
        Rec memory r = Rec("k", "ab", "xyz", "s");
        assert(r.tag == "ab" && r.b.length == 3 && r.b[2] == "z");
    }
    // a storage string copied to memory: the copy's length is the stored one
    /// @custom:key box
    function copyLength() public {
        name = "xyz";
        string memory c = name;
        assert(bytes(c).length == 3 && bytes(c)[2] == "z");
    }
    /// @custom:key box
    function copyLengthSymbolic() public view {
        string memory c = name;
        assert(bytes(c).length == bytes(name).length);
    }
}
