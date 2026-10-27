contract Group07Mixed {
    uint[2] stored;
    uint[2][] rows;
    function aliases() public {
        stored[0] = 7;
        uint[2] memory y; y[0] = 2;
        uint[2] memory a = true ? y : stored;
        a[0] = 9;
        assert(y[0] == 9 && stored[0] == 7);
        uint[2] memory b = false ? stored : y;
        b[0] = 11;
        assert(y[0] == 11 && a[0] == 11 && stored[0] == 7);
    }
    function snapshots() public {
        stored[0] = 7;
        uint[2] memory y; y[0] = 2;
        uint[2] memory a = false ? y : stored;
        uint[2] memory b = true ? stored : y;
        stored[0] = 13; a[0] = 17;
        assert(b[0] == 7 && a[0] == 17 && y[0] == 2 && stored[0] == 13);
    }
    function lazyPaths() public {
        stored[0] = 7;
        uint[2][] memory empty = new uint[2][](0);
        uint[2] memory a = true ? stored : empty[99];
        uint[2] memory b = false ? rows[99] : a;
        assert(a[0] == 7 && b[0] == 7 && rows.length == 0);
    }
    function selectedFailure() public {
        uint[2][] memory empty = new uint[2][](0);
        uint[2] memory a = false ? stored : empty[99];
        a[0] = 1;
    }
    function conditionOnce() public {
        stored[0] = 7; uint i = 0;
        uint[2] memory y;
        uint[2] memory a = i++ == 0 ? stored : y;
        assert(i == 1 && a[0] == 7);
    }
    function effectfulPaths() public {
        rows.push(); rows[0][0] = 7;
        uint[2][] memory ms = new uint[2][](1); ms[0][0] = 2;
        uint i = 0; uint j = 0;
        uint[2] memory a = true ? rows[i++] : ms[j++];
        assert(i == 1 && j == 0 && a[0] == 7);
        uint[2] memory b = false ? rows[i++] : ms[j++];
        b[0] = 5;
        assert(i == 1 && j == 1 && ms[0][0] == 5 && a[0] == 7);
    }
    function nested() public {
        stored[0] = 7; uint[2] memory y; y[0] = 2;
        uint[2] memory a = true ? (false ? y : stored) : y;
        stored[0] = 13; a[0] = 17;
        assert(y[0] == 2 && a[0] == 17 && stored[0] == 13);
    }
    function falseControl() public {
        stored[0] = 7; uint[2] memory y; y[0] = 2;
        uint[2] memory a = false ? y : stored;
        a[0] = 9;
        assert(stored[0] == 9);
    }
    function calldataEscape(uint[2] calldata c) external {
        uint[2] memory m = c;
        uint[2] memory a = true ? m : stored;
        a[0] = 1;
    }
    function memoryArm() internal returns (uint[2] memory) {
        stored[1] += 1; uint[2] memory a; a[0] = 19; return a;
    }
    function storageArm() internal returns (uint[2] storage) {
        stored[1] += 10; return stored;
    }
    function effectfulCalls() public {
        stored[0] = 7; stored[1] = 0;
        uint[2] memory a = true ? memoryArm() : stored;
        assert(stored[1] == 1 && a[0] == 19);
        uint[2] memory b = false ? memoryArm() : storageArm();
        b[0] = 31;
        assert(stored[1] == 11 && stored[0] == 7 && a[0] == 19 && b[0] == 31);
    }
    string storedString;
    function stringEffects() public {
        storedString = "ab"; uint i = 0;
        string[] memory ms = new string[](1); ms[0] = "cd";
        string memory a = true ? storedString : ms[i++];
        string memory b = false ? storedString : ms[i++];
        assert(i == 1 && bytes(a)[0] == "a" && bytes(b)[0] == "c");
    }
    function copiedBoundsFailure() public {
        uint[2] memory y; uint[2] memory a = false ? y : stored;
        uint i = 2; uint r = a[i]; assert(r == 0);
    }
}
