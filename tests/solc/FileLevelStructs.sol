pragma solidity ^0.8.0;

struct FileLevelPair { uint left; uint right; }
struct Pair { uint a; bool b; }

library FilePairLib {
    function swap(FileLevelPair storage p) internal {
        uint saved = p.left;
        p.left = p.right;
        p.right = saved;
    }
}

contract FileLevelStructs {
    FileLevelPair pair;

    function swaps() public {
        pair.left = 1;
        pair.right = 2;
        FilePairLib.swap(pair);
        assert(pair.left == 2 && pair.right == 1);
    }

    function falsePost() public {
        pair.left = 1;
        pair.right = 2;
        FilePairLib.swap(pair);
        assert(pair.left == 1);
    }
}

contract OwnStructWins {
    struct Pair { uint a; uint b; }
    Pair pair;

    function ownPair() public {
        pair.a = 7;
        pair.b = 8;
        assert(pair.a + pair.b == 15);
    }
}

contract DifferentFileStruct {
    Pair pair;

    function unsupportedShape() public {
        pair.b = true;
        assert(pair.b);
    }
}

contract DifferentOwnStruct {
    struct FileLevelPair { uint left; bool right; }
    FileLevelPair pair;

    function unsupportedShape() public {
        pair.right = true;
        assert(pair.right);
    }
}
