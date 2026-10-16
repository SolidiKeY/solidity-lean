pragma solidity ^0.8.0;

struct Sub { uint8 x; uint y; }
struct WithSub { uint a; Sub sub; }
struct FileLevelPair { uint left; uint right; }

contract InvalidNestedStruct {
    WithSub value;

    function narrowMember() public {
        value.sub.x = 255;
        value.sub.x++;
        uint result = value.sub.x;
        assert(result == 256);
    }
}

library HiddenStructLib {
    struct FileLevelPair { uint left; uint8 right; }

    function narrowMember() internal {
        FileLevelPair memory value;
        value.right = 255;
        value.right++;
        uint result = value.right;
        assert(result == 256);
    }
}

contract HiddenStructCaller {
    function narrowLibraryMember() public {
        HiddenStructLib.narrowMember();
    }
}
