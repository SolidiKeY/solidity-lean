// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
// A contract's own structs, none of them the struct table's: nested, with a
// mapping member, in an array, built by a struct literal, a narrow member,
// and two that share a table struct's name with other members.
struct Point { uint x; uint y; }

contract OwnStructs {
    struct Line { Point start; Point stop; uint8 width; }
    struct Account { uint balance; mapping(uint => uint) allowance; }
    struct Pair { uint a; bool b; }
    Line line;
    Line[] lines;
    mapping(uint => Account) accounts;
    Pair pair;

    function nested() public {
        line.start.x = 1;
        line.stop.y = 2;
        assert(line.start.x + line.stop.y == 3);
    }

    function mappingMember() public {
        accounts[7].balance = 5;
        accounts[7].allowance[3] = 9;
        delete accounts[7];
        assert(accounts[7].balance == 0 && accounts[7].allowance[3] == 9);
    }

    function arrayOfStructs() public {
        delete lines;
        lines.push();
        lines[0].width = 3;
        lines[0].stop.x = 4;
        assert(lines.length == 1 && lines[0].width == 3 && lines[0].stop.x == 4);
    }

    function literal() public {
        Point memory p = Point(4, 5);
        line.start = p;
        assert(line.start.x == 4 && line.start.y == 5);
    }

    function namedLiteral() public {
        pair = Pair({b: true, a: 2});
        assert(pair.b && pair.a == 2);
    }

    /// @custom:key box
    function narrowOverflow() public {
        line.width = 255;
        line.width += 1;
        assert(false);
    }

    function falsePost() public {
        line.start.x = 1;
        assert(line.start.x == 2);
    }
}
