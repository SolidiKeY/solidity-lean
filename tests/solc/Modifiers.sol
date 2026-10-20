// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract Modifiers {
    uint total = 2;
    uint out;
    uint8[] stored;
    modifier nonZero(uint x) { require(x > 0); _; }
    modifier around() { total = total + 1; _; total = total + 10; }
    modifier doubleAfter() { _; total = total * 2; }
    modifier addThreeAfter() { _; total = total + 3; }
    modifier setsFive() { total = 5; _; }
    modifier record(uint x) { out = x; _; }
    modifier keepsLocal(uint x) { uint c = x; _; out = c; }
    modifier twice() { _; _; }
    modifier narrow(uint8 x) { x += 1; _; }
    modifier narrowArray(uint8[] memory xs) { xs[0] += 1; assert(xs[0] == 1); _; }
    modifier narrowArrayMax(uint8[] memory xs) { xs[0] = 255; xs[0] += 1; _; }
    modifier storedMax(uint8[] storage xs) { xs.push(255); xs[xs.length - 1] += 1; _; }
    modifier unnamed(uint) { _; }
    function setOne() internal { total = 1; }
    modifier callsInternal() { setOne(); _; }
    function guarded(uint x) internal pure nonZero(x) returns (uint) { return x; }
    function returnsEarly() internal around returns (uint r) { r = total; return r; }
    function ordered() internal doubleAfter addThreeAfter { total = 1; }
    function localScopes() internal keepsLocal(2) keepsLocal(5) {}
    function repeated() internal twice { total = total + 1; }
    function consume() internal unnamed(total++) {}
    /// @custom:key box
    constructor() around { assert(total == 3); total = 4; }
    /// @custom:key box
    function arguments() public pure { assert(guarded(3) == 3); }
    /// @custom:key box
    function resumesAfterReturn() public {
        total = 0;
        uint r = returnsEarly();
        assert(r == 1 && total == 11);
    }
    /// @custom:key box
    function firstListedOutermost() public { ordered(); assert(total == 8); }
    /// @custom:key box
    function directApplication() public setsFive { assert(total == 5); }
    /// @custom:key box
    function falsePost() public setsFive { assert(total == 6); }
    /// @custom:key box
    function argumentEvaluation() public setsFive record(total) { assert(out == 5); }
    /// @custom:key box
    function localsPerApplication() public { localScopes(); assert(out == 2); }
    /// @custom:key box
    function multiplePlaceholders() public { total = 0; repeated(); assert(total == 2); }
    /// @custom:key box
    function internalCallFromModifier() public callsInternal { assert(total == 1); }
    function narrowModifierGap() public narrow(255) {}
    // a reference parameter is a local at its location, of its narrow positions
    function narrowArrayModifier() public narrowArray(new uint8[](1)) {}
    /// @custom:key box
    function narrowArrayModifierPanics() public narrowArrayMax(new uint8[](1)) { assert(false); }
    /// @custom:key box
    function storageArrayModifierPanics() public storedMax(stored) { assert(false); }
    /// @custom:key box
    function unnamedParameter() public unnamed(1) { assert(true); }
    /// @custom:key box
    function unnamedArgumentStillRuns() public {
        total = 0;
        consume();
        assert(total == 1);
    }
}
