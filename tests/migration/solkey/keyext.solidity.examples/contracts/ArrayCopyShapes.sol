// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract ArrayCopyShapes {
    struct Box { uint[3] items; uint tag; }

    uint[3] small;
    uint[5] big;
    uint[] source;
    uint[] target;
    uint[2][2] smallGrid;
    uint[3][3] bigGrid;
    Box sourceBox;
    Box targetBox;

    function fixedCopyKeepsTargetLengthAndClearsTail() public {
        small[0] = 11;
        small[1] = 12;
        small[2] = 13;
        big[3] = 93;
        big[4] = 94;
        big = small;
        assert(small.length == 3);
        assert(big.length == 5);
        assert(big[0] == 11);
        assert(big[2] == 13);
        assert(big[3] == 0);
        assert(big[4] == 0);
        small[0] = 99;
        assert(big[0] == 11);
    }

    function fixedToDynamicCopyTakesSourceLength() public {
        small[0] = 11;
        small[2] = 13;
        target = small;
        assert(target.length == 3);
        assert(target[0] == 11);
        assert(target[2] == 13);
        target.push();
        assert(target.length == 4);
        assert(target[3] == 0);
        assert(small.length == 3);
    }

    function dynamicShrinkClearsReusedSlot() public {
        delete source;
        delete target;
        source.push(11);
        source.push(12);
        target.push(91);
        target.push(92);
        target.push(93);
        target = source;
        assert(target.length == 2);
        assert(target[0] == 11);
        assert(target[1] == 12);
        target.push();
        assert(target.length == 3);
        assert(target[2] == 0);
        target[0] = 99;
        assert(source[0] == 11);
    }

    function nestedFixedCopyClearsInnerAndOuterTails() public {
        smallGrid[0][0] = 11;
        smallGrid[0][1] = 12;
        smallGrid[1][0] = 21;
        smallGrid[1][1] = 22;
        bigGrid[0][2] = 93;
        bigGrid[1][2] = 94;
        bigGrid[2][0] = 95;
        bigGrid[2][2] = 96;
        bigGrid = smallGrid;
        assert(bigGrid.length == 3);
        assert(bigGrid[0].length == 3);
        assert(bigGrid[2].length == 3);
        assert(bigGrid[0][1] == 12);
        assert(bigGrid[1][1] == 22);
        assert(bigGrid[0][2] == 0);
        assert(bigGrid[1][2] == 0);
        assert(bigGrid[2][0] == 0);
        assert(bigGrid[2][2] == 0);
    }

    function structCopyPreservesFixedMemberShape() public {
        sourceBox.items[0] = 11;
        sourceBox.items[1] = 12;
        sourceBox.items[2] = 13;
        sourceBox.tag = 7;
        targetBox.items[2] = 99;
        targetBox.tag = 8;
        targetBox = sourceBox;
        assert(targetBox.items.length == 3);
        assert(targetBox.items[0] == 11);
        assert(targetBox.items[2] == 13);
        assert(targetBox.tag == 7);
        sourceBox.items[2] = 42;
        assert(targetBox.items[2] == 13);
    }

    function selfCopyThroughAliasPreservesValues() public {
        big[0] = 11;
        big[4] = 15;
        uint[5] storage same = big;
        big = same;
        assert(big.length == 5);
        assert(big[0] == 11);
        assert(big[4] == 15);
    }

    function storageAliasWritesOriginal() public {
        uint[3] storage same = small;
        same[2] = 31;
        assert(same.length == 3);
        assert(small[2] == 31);
    }
}
