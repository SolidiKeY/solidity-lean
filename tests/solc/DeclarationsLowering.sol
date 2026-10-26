pragma solidity ^0.8.38;
contract DeclarationBase {
    uint private x = 3;
    function base() internal returns (uint) { x += 1; return x; }
}
contract DeclarationsLowering is DeclarationBase {
    uint private x = 7;
    uint y = 2;
    bytes2 constant marker = 0x1234;
    int8 constant signedMarker = -7;
    function constantKinds() public pure returns (bool) {
        return abi.encodePacked(marker).length == 2 && abi.encodePacked(signedMarker).length == 1;
    }
    int8 immutable small = -7;
    function qualified() public returns (uint) { return base() + x + DeclarationsLowering.y; }
    function signedLiteral() public view returns (int) { return small; }
    function shadow() public pure returns (uint) {
        uint x = 3;
        { uint x = x; x += 1; }
        return x;
    }
}
contract EffectfulImmutable {
    uint calls;
    uint8 immutable a = init();
    function init() internal returns (uint8) { calls++; return 2; }
    function value() public view returns (uint) { return a; }
    function count() public view returns (uint) { return calls; }
}
contract ExcludedImmutable {
    uint immutable a = block.number;
    constructor() {}
    function value() public view returns (uint) { return a; }
}

library InvalidForeign {
    struct Bad { Bad[] children; }
    struct Outer { Bad nested; }
}
contract InvalidTransitive {
    InvalidForeign.Outer box;
    function value() public view returns (uint) { return box.nested.children.length; }
}
contract DynamicDiscard {
    uint calls;
    function callable() public pure {}
    function receiver() internal returns (DynamicDiscard) { calls++; return this; }
    function value() public returns (uint) { receiver().callable; return calls; }
}

library ExcludedModifier {
    modifier bad() { block.number; _; }
    function read() internal bad returns (uint) { return 7; }
}
contract ModifierAdmission {
    function value() public returns (uint) { return ExcludedModifier.read(); }
}

contract InitA {
    uint immutable x = x + 1;
    uint immutable y = x += 2;
    constructor(uint) m(x += 16) m(x += 32) { x += 64; x += 128; }
    modifier m(uint) { _; }
    function get() public returns (uint) { return x; }
}
contract InitB is InitA(InitA.x += 8) { constructor(uint) {} }
contract InitSequence is InitB {
    constructor() InitB(x += 4) {}
    function observed() public returns (uint) { return get(); }
}

contract ForwardImmutable {
    uint8 immutable earlier = later;
    uint8 immutable later = 2;
    function observed() public view returns (uint, uint) { return (earlier, later); }
}
contract IndirectForwardImmutable {
    uint8 immutable earlier = readLater();
    uint8 immutable later = 2;
    constructor() {}
    function readLater() internal view returns (uint8) { return later; }
    function observed() public view returns (uint) { return earlier; }
}
contract Other {}
contract UnsupportedImmutable {
    uint calls;
    Other immutable ignored = Other(address(uint160(calls++)));
    constructor() {}
    function observed() public view returns (uint) { return calls; }
}

abstract contract ForwardBase {
    uint observedValue;
    constructor() { observedValue = read(); }
    function read() internal virtual returns (uint);
}
contract ForwardDerived is ForwardBase {
    uint8 immutable later = 2;
    function read() internal override returns (uint) { return later; }
    function observed() public view returns (uint) { return observedValue; }
}
contract EntryBase {
    function chosen() public pure virtual returns (uint) { return 1; }
    function inherited() public pure returns (uint) { return 3; }
    function hidden() internal pure returns (uint) { return 9; }
}
contract EntryDerived is EntryBase {
    function chosen() public pure override returns (uint) { return 2; }
}

contract EffectfulForwardDerived is ForwardBase {
    uint immutable later = make();
    function make() internal pure returns (uint) { return 2; }
    function read() internal view override returns (uint) { return later; }
    function observed() public view returns (uint) { return observedValue; }
}

contract ArgumentBase {
    uint internal immutable x = make();
    uint internal seen;
    constructor(uint a) { seen = a; }
    function make() internal pure returns (uint) { return 2; }
}
contract ArgumentDerived is ArgumentBase {
    constructor() ArgumentBase(x) {}
    function observed() public view returns (uint) { return seen; }
}
contract ImplicitPhaseBase { uint internal baseValue = 3; }
contract ImplicitPhaseDerived is ImplicitPhaseBase {
    uint immutable value = baseValue + 2;
    function observed() public view returns (uint) { return value; }
}

contract StringArrayERC {
    function test() public pure returns (bool) {
        return erc7201(["x"][0]) == erc7201(["y", "x"][1]);
    }
}

contract ImplicitUnsupportedInitialization {
    uint immutable ignored = block.number;
    function observed() public pure returns (uint) { return 7; }
}

contract CallbackTarget { function callMe() public returns (uint) { return 2; } }
contract CallbackBase {}
contract InitializerCallback is CallbackBase {
    uint immutable value = externalInit();
    function externalInit() internal returns (uint) { return CallbackTarget(address(0)).callMe(); }
    function observed() public view returns (uint) { return value; }
}
