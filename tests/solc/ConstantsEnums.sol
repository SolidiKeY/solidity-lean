// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
uint constant FILE_LIMIT = 4;
enum FileColor { Red, Green, Blue }
type Wei is uint;
type Decision is bool;
type Payee is address;
library ConstantsLib { uint constant UNIT = 10; }
contract ConstantsEnums {
    enum Phase { Open, Closed }
    uint constant LIMIT = FILE_LIMIT + 3;
    bool constant YES = true;
    uint immutable deployed = 9;
    address owner;
    /// @custom:key box
    function constantsInline() public pure {
        assert(LIMIT == 7);
        assert(ConstantsEnums.LIMIT == 7);
        assert(ConstantsLib.UNIT == 10);
        assert(2 * LIMIT == 14);
        assert(YES);
    }
    function defaultPhase() internal pure returns (Phase) {}
    /// @custom:key box
    function enumsHaveOrdinals() public pure {
        Phase p = Phase.Closed;
        FileColor c = FileColor.Blue;
        assert(p == ConstantsEnums.Phase.Closed);
        assert(uint(c) == 2);
        assert(defaultPhase() == Phase.Open);
    }
    /// @custom:key box
    function reservedLocal() public view {
        address payable to = payable(owner);
        assert(to == owner);
    }
    /// @custom:key box
    function falsePost() public pure { assert(LIMIT == 8); }
    /// @custom:key box
    function boundsAndValueTypes() public pure {
        uint8 hi = type(uint8).max;
        int8 lo = type(int8).min;
        int expected = -128;
        assert(hi == 255 && lo == expected);
        assert(uint(type(FileColor).max) == 2);
        Wei w = Wei.wrap(3);
        assert(Wei.unwrap(w) == 3);
    }
    /// @custom:key box
    function boundsFalsePost() public pure { assert(type(uint8).max == 254); }
    /// @custom:key box
    function otherValueTypes(address who) public pure {
        Decision yes = Decision.wrap(true);
        assert(Decision.unwrap(yes));
        Payee p = Payee.wrap(who);
        assert(Payee.unwrap(p) == who);
    }
    /// @custom:key box
    function immutableGap() public view { assert(deployed == 9); }
}
