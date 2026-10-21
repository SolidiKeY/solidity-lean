// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// `calldata` parameters (docs/semantic-gaps.md, "Bytes and strings"): a
// memory parameter the body cannot write (solc refuses a write, and so does
// the elaborator), read as a memory one is.
contract Calldata {
    /// @custom:key box
    function first(uint[] calldata xs) external pure returns (uint) {
        require(xs.length > 0);
        return xs[0];
    }

    /// @custom:key box
    function sumTwo(uint[] calldata xs) external pure {
        require(xs.length >= 2);
        uint s = xs[0] + xs[1];
        assert(s >= xs[0]);
    }

    function byteLength(bytes calldata b) external pure returns (uint) {
        return b.length;
    }

    function hashOf(bytes calldata b) external pure {
        assert(keccak256(b) == keccak256(b));
    }

    function strLength(string calldata s) external pure returns (uint) {
        return bytes(s).length;
    }

    struct P { uint a; bool f; }
    /// @custom:key box
    function member(P calldata p) external pure returns (uint) {
        return p.f ? p.a : 0;
    }

    // a calldata parameter handed to a function that reads it
    function head(uint[] memory ys) internal pure returns (uint) {
        return ys.length == 0 ? 0 : ys[0];
    }
    /// @custom:key box
    function passes(uint[] calldata xs) external pure {
        require(xs.length > 0);
        assert(head(xs) == xs[0]);
    }

    // a memory alias of calldata that is only read
    /// @custom:key box
    function readAlias(uint[] calldata xs) external pure {
        uint[] memory m = xs;
        require(m.length > 0);
        assert(m[0] == xs[0]);
    }

    // a memory copy of calldata that is written: solc copies, the model would
    // share the object, so the elaborator refuses it (`calldataCheck`)
    function writesCopy(uint[] calldata xs) external pure {
        uint[] memory m = xs;
        m[0] = 1;
    }

    // a calldata local bound to a parameter: read only too
    /// @custom:key box
    function localAlias(uint[] calldata xs) external pure {
        uint[] calldata ys = xs;
        require(ys.length > 0);
        assert(ys[0] == xs[0]);
    }

    // a slice: refused (a copy element by element, a loop)
    function tail(bytes calldata b) external pure returns (uint) {
        bytes calldata t = b[4:];
        return t.length;
    }
}
