// SPDX-License-Identifier: MIT
pragma solidity >=0.8.34 <0.9.0;

// Error arguments are evaluated even when require's condition is false.
// The deliberately wrong assertions are negative tests, never proof goals.
contract CallExceptions {
    error E(uint256 x);
    error Sel(bytes4 selector);
    error Signed(int256 x);
    error Pair(uint256 first, uint8 second);
    error Snapshot(uint256 beforeEffect, uint256 afterEffect);
    event Seen(uint256 x);
    enum Mode { A, B }
    uint256 ticks;

    function failAssert() internal pure returns (uint256 r) { assert(false); return 0; }
    function tick() internal returns (uint256 r) { ticks += 1; return ticks; }
    function identity(uint256 x) internal pure returns (uint256 r) { return x; }
    function failReason() internal pure returns (string memory r) { assert(false); return "unused"; }

    function requireTrueArg() external pure { require(true, E(failAssert())); }
    function requireFalseArg() external pure { require(false, E(failAssert())); }
    function revertArg() external pure { revert E(failAssert()); }
    function emitArg() external { emit Seen(failAssert()); }
    function signedLiteral() external pure { revert Signed(2 ** 3); }
    function signedPayload() external {
        try this.signedLiteral() { assert(false); }
        catch (bytes memory d) { assert(d.length == 36 && d[35] == 0x08); }
    }
    function totalTrue() external pure { require(true, E(7)); }
    function totalFalse() external pure { require(false, E(7)); }
    function trueEffect() external {
        ticks = 0;
        require(true, E(tick()));
        assert(ticks == 1);
    }
    function falseEffectExpectation() external {
        ticks = 0;
        require(true, E(tick()));
        assert(ticks == 0);
    }
    function failureOrder(uint256 x, uint8 y) external pure {
        require(false, Pair(1 / x, y + 1));
    }
    function reasonOrder(uint256 x) external pure {
        require(1 / x > 0, failReason());
    }
    function enumRead(uint256 x) external pure returns (uint256 r) {
        Mode m = Mode(x);
        return uint256(m);
    }
    function unsetCall(uint256 x) external pure returns (uint256 r) {
        function (uint256) internal pure returns (uint256) h;
        return h(x);
    }
    function unsetArg() external pure returns (uint256 r) {
        function (uint256) internal pure returns (uint256) h;
        return h(failAssert());
    }
    function assignedCall() external pure returns (uint256 r) {
        function (uint256) internal pure returns (uint256) h = identity;
        return h(7);
    }
    function echo(uint256 x) external pure returns (uint256 r) { return x; }
    function selectorArg() external view { require(true, Sel(this.echo.selector)); }
    function selectorFail() external view { require(false, Sel(this.echo.selector)); }
    function callerArgument() external returns (uint256 r) {
        try this.echo(failAssert()) returns (uint256 x) { return x; }
        catch { return 999; }
    }
    function failureCode() external returns (uint256 r) {
        try this.failureOrder(0, 255) { return 0; }
        catch Panic(uint256 code) { return code; }
        catch { return 999; }
    }
    function reasonCode() external returns (uint256 r) {
        try this.reasonOrder(0) { return 0; }
        catch Panic(uint256 code) { return code; }
        catch { return 999; }
    }
    function enumCode() external returns (uint256 r) {
        try this.enumRead(2) returns (uint256 x) { return x; }
        catch Panic(uint256 code) { return code; }
        catch { return 999; }
    }
    function unsetCode() external returns (uint256 r) {
        try this.unsetCall(7) returns (uint256 x) { return x; }
        catch Panic(uint256 code) { return code; }
        catch { return 999; }
    }
    function unsetArgCode() external returns (uint256 r) {
        try this.unsetArg() returns (uint256 x) { return x; }
        catch Panic(uint256 code) { return code; }
        catch { return 999; }
    }
    function rawEnumPayload() external {
        try this.enumRead(2) returns (uint256) { assert(false); }
        catch (bytes memory d) {
            assert(d.length == 36);
            assert(d[0] == 0x4e && d[1] == 0x48 && d[2] == 0x7b && d[3] == 0x71);
            assert(d[35] == 0x21);
        }
    }
    function rawUnsetPayload() external {
        try this.unsetCall(7) returns (uint256) { assert(false); }
        catch (bytes memory d) {
            assert(d.length == 36);
            assert(d[0] == 0x4e && d[3] == 0x71 && d[35] == 0x51);
        }
    }
    function wrongEnumCode() external {
        try this.enumRead(2) returns (uint256) { assert(false); }
        catch Panic(uint256 code) { assert(code == 1); }
        catch { assert(false); }
    }
    function wrongUnsetCode() external {
        try this.unsetCall(7) returns (uint256) { assert(false); }
        catch Panic(uint256 code) { assert(code == 1); }
        catch { assert(false); }
    }
    function wrongFailureCode() external {
        try this.failureOrder(0, 255) { assert(false); }
        catch Panic(uint256 code) { assert(code == 17); }
        catch { assert(false); }
    }
    function snapshotFail() external { revert Snapshot(ticks, tick()); }
    function snapshot() external {
        ticks = 5;
        try this.snapshotFail() { assert(false); }
        catch (bytes memory d) {
            assert(ticks == 5);
            assert(d.length == 68 && d[35] == 0x05 && d[67] == 0x06);
        }
    }
    function writeThenFail() external { ticks = 9; require(false, E(tick())); }
    function rollback() external {
        ticks = 3;
        try this.writeThenFail() { assert(false); }
        catch (bytes memory d) {
            assert(ticks == 3);
            assert(d.length == 36 && d[35] == 0x0a);
        }
    }

    // Fixed-byte custom-error words are left-aligned, including leading zeroes.
    error SmallBytes(bytes2 value);
    error WideBytes(bytes4 value);
    error FullBytes(bytes32 value);
    error BytesSnapshot(bytes2 beforeEffect, uint256 afterEffect);
    bytes2 savedBytes;
    function smallLiteralFail() external pure { revert SmallBytes(hex"00ab"); }
    function smallDynamicFail(bytes2 b) external pure { revert SmallBytes(b); }
    function wideBytesFail(bytes2 b) external pure { revert WideBytes(b); }
    function twoBytes() internal pure returns (bytes2 r) { return hex"abcd"; }
    function returnedBytesFail() external pure { revert WideBytes(twoBytes()); }
    function fullBytesFail() external pure { revert FullBytes(bytes32(bytes2(0x00ab))); }
    function requireBytesFail(bytes2 b) external pure { require(false, WideBytes(b)); }
    function requireBytesTrue() external pure { require(true, SmallBytes(hex"00ab")); }
    function changeBytes() internal returns (uint256 r) { savedBytes = hex"0000"; return tick(); }
    function bytesSnapshotFail() external { revert BytesSnapshot(savedBytes, changeBytes()); }
    function customBytesPayloads() external {
        try this.smallLiteralFail() { assert(false); }
        catch (bytes memory d) { assert(d.length == 36 && d[4] == 0x00 && d[5] == 0xab && d[6] == 0x00 && d[35] == 0x00); }
        try this.smallDynamicFail(bytes2(0xabcd)) { assert(false); }
        catch (bytes memory d) { assert(d.length == 36 && d[4] == 0xab && d[5] == 0xcd && d[6] == 0x00 && d[35] == 0x00); }
        try this.wideBytesFail(bytes2(0xabcd)) { assert(false); }
        catch (bytes memory d) { assert(d.length == 36 && d[4] == 0xab && d[5] == 0xcd && d[6] == 0x00 && d[7] == 0x00 && d[35] == 0x00); }
        try this.requireBytesFail(bytes2(0xabcd)) { assert(false); }
        catch (bytes memory d) { assert(d.length == 36 && d[4] == 0xab && d[5] == 0xcd && d[6] == 0x00 && d[35] == 0x00); }
        this.requireBytesTrue();
        try this.returnedBytesFail() { assert(false); }
        catch (bytes memory d) { assert(d.length == 36 && d[4] == 0xab && d[5] == 0xcd && d[6] == 0x00 && d[35] == 0x00); }
        try this.fullBytesFail() { assert(false); }
        catch (bytes memory d) { assert(d.length == 36 && d[4] == 0x00 && d[5] == 0xab && d[35] == 0x00); }
        bytes4 s = this.echo.selector;
        try this.selectorFail() { assert(false); }
        catch (bytes memory d) {
            assert(d.length == 36 && d[4] == s[0] && d[5] == s[1] && d[6] == s[2] && d[7] == s[3] && d[35] == 0x00);
        }
        savedBytes = hex"abcd";
        ticks = 5;
        try this.bytesSnapshotFail() { assert(false); }
        catch (bytes memory d) {
            assert(ticks == 5 && savedBytes == hex"abcd" && d.length == 68 && d[4] == 0xab && d[5] == 0xcd && d[35] == 0x00 && d[67] == 0x06);
        }
    }
    function wrongCustomBytesPayload() external {
        try this.smallLiteralFail() { assert(false); }
        catch (bytes memory d) { assert(d[35] == 0xab); }
    }
}
