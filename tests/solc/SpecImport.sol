// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract SpecImport {
    modifier unparsed(uint a, uint b) { assembly { pop(add(a, b)) } _; }

    /// @custom:key ensures true -> \forall uint q; q == q
    function universalConsequent() public pure {}

    /// @custom:key ensures false -> \exists uint q; q == 0
    function existentialConsequent() public pure {}

    /// @custom:key ensures true -> \forall uint q; q == 0
    function falseUniversal() public pure {}

    /// @custom:key requires from > 0
    function renamedSpec(uint from) public pure { assert(from > 0); }

    function omittedCaller(uint x) public pure { renamedSpec(x); assert(false); }

    /// @custom:key ensures false; requires false
    function omittedBody() public pure { assembly {} }

    function omittedModifier(uint a, uint b) public unparsed(a, b) { assert(false); }

    function stillChecked() public pure { assert(false); }
}

contract SpecCtorGap {
    uint marker = 1;
    /// @custom:key requires from > 0
    constructor(uint from) { marker = from; }
    function stillChecked() public pure { assert(false); }
}

contract OmittedTypes {
    string title;
    uint8[] narrow;
    mapping(uint8 => uint) narrowKeys;
    mapping(uint => uint8) narrowValues;
    function unrelated() public pure { assert(true); }
    function stillChecked() public pure { assert(false); }
    function readsString() public view { string memory s = title; }
    function readsNarrow() public view { uint x = narrow[0]; }
    function readsNarrowKey() public view { uint x = narrowKeys[0]; }
    function readsNarrowValue() public view { uint x = narrowValues[0]; }
    /// @custom:key ensures narrow.length == 0
    function specReadsNarrow() public view {}
}
