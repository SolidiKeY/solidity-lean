pragma solidity ^0.8.0;

contract ArrayShapes {
    struct Basket { uint[] items; }
    uint[2] small;
    uint[4] big;
    uint[] dynamicValues;
    uint[2][2] sources;
    uint[4][] targets;
    uint[][] rows;
    Basket basket;

    function fixedTail() public {
        small[0] = 11;
        small[1] = 12;
        big[3] = 99;
        big = small;
        assert(big.length == 4 && big[0] == 11 && big[1] == 12);
        assert(big[2] == 0 && big[3] == 0);
        small[0] = 88;
        assert(big[0] == 11);
        big[1] = 77;
        assert(small[1] == 12);
    }

    function dynamicLength() public {
        small[1] = 12;
        dynamicValues = small;
        assert(dynamicValues.length == 2 && dynamicValues[1] == 12);
        dynamicValues.push();
        assert(dynamicValues.length == 3 && dynamicValues[2] == 0);
    }

    function fieldTarget() public {
        small[0] = 21;
        basket.items = small;
        assert(basket.items.length == 2 && basket.items[0] == 21);
    }

    function sourceAndTargetEffects() public {
        delete targets;
        targets.push();
        targets.push();
        sources[0][0] = 31;
        uint i = 0;
        targets[i++] = sources[i++];
        assert(i == 2 && targets[1][0] == 31 && targets[1][3] == 0);
    }

    function pushedShape() public {
        delete rows;
        small[0] = 41;
        rows.push(small);
        assert(rows.length == 1 && rows[0].length == 2 && rows[0][0] == 41);
        small[0] = 42;
        assert(rows[0][0] == 41);
    }

    function falseTail() public {
        big = small;
        assert(big[3] == 1);
    }

    function falseAlias() public {
        small[0] = 1;
        dynamicValues = small;
        small[0] = 9;
        assert(dynamicValues[0] == 9);
    }

    /// @custom:key box
    function badSourceReverts() public {
        uint i = 2;
        dynamicValues = sources[i];
        assert(false);
    }
}
