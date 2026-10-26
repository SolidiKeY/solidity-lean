// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

// The custom meanings deliberately disagree with the builtin operators.
type N is uint8;
using {mixN as +, subN as -, mulN as *, divN as /, remN as %, andN as &, orN as |, xorN as ^, eqN as ==, neN as !=, ltN as <, leN as <=, gtN as >, geN as >=, negN as -, notN as ~} for N global;

function mixN(N a, N b) pure returns (N) { return N.wrap(N.unwrap(a)*10+N.unwrap(b)); }
function subN(N a, N b) pure returns (N) { return N.wrap(N.unwrap(a)+N.unwrap(b)); }
function mulN(N a, N b) pure returns (N) { return N.wrap(N.unwrap(a)+N.unwrap(b)+1); }
function divN(N a, N b) pure returns (N) { return N.wrap(N.unwrap(a)+N.unwrap(b)+2); }
function remN(N a, N b) pure returns (N) { return N.wrap(N.unwrap(a)+N.unwrap(b)+3); }
function andN(N a, N b) pure returns (N) { return N.wrap(N.unwrap(a)|N.unwrap(b)); }
function orN(N a, N b) pure returns (N) { return N.wrap(N.unwrap(a)&N.unwrap(b)); }
function xorN(N a, N b) pure returns (N) { return N.wrap(N.unwrap(a)+N.unwrap(b)); }
function eqN(N a, N b) pure returns (bool) { return N.unwrap(a) != N.unwrap(b); }
function neN(N a, N b) pure returns (bool) { return N.unwrap(a) == N.unwrap(b); }
function ltN(N a, N b) pure returns (bool) { return N.unwrap(a) > N.unwrap(b); }
function leN(N a, N b) pure returns (bool) { return N.unwrap(a) >= N.unwrap(b); }
function gtN(N a, N b) pure returns (bool) { return N.unwrap(a) < N.unwrap(b); }
function geN(N a, N b) pure returns (bool) { return N.unwrap(a) <= N.unwrap(b); }
function negN(N a) pure returns (N) { return N.wrap(N.unwrap(a) + 1); }
function notN(N a) pure returns (N) { return N.wrap(N.unwrap(a) + 3); }

type Other is uint8;
using {mixOther as +} for Other global;
function mixOther(Other a, Other b) pure returns (Other) {
    return Other.wrap(Other.unwrap(a) + Other.unwrap(b) + 100);
}

type Flag is bool;
using {notFlag as ~, eqFlag as ==, andFlag as &} for Flag global;
function notFlag(Flag a) pure returns (Flag) { return Flag.wrap(!Flag.unwrap(a)); }
function andFlag(Flag a, Flag b) pure returns (Flag) { return Flag.wrap(Flag.unwrap(a) && Flag.unwrap(b)); }
function eqFlag(Flag a, Flag b) pure returns (bool) {
    return !Flag.unwrap(a) || Flag.unwrap(b);
}

type Bits is bytes2;
using {xorBits as ^} for Bits global;
function xorBits(Bits a, Bits b) pure returns (Bits) {
    return Bits.wrap(Bits.unwrap(a) | Bits.unwrap(b));
}

type Signed is int16;
using {negSigned as -} for Signed global;
function negSigned(Signed a) pure returns (Signed) { return Signed.wrap(Signed.unwrap(a) + 1); }

type Account is address;
using {eqAccount as ==} for Account global;
function eqAccount(Account a, Account b) pure returns (bool) {
    return Account.unwrap(a) != Account.unwrap(b);
}

type Payee is address payable;
using {eqPayee as ==} for Payee global;
function eqPayee(Payee a, Payee b) pure returns (bool) {
    return Payee.unwrap(a) != Payee.unwrap(b);
}

type Wrapping is uint8;
using {addWrapping as +} for Wrapping global;
function addWrapping(Wrapping a, Wrapping b) pure returns (Wrapping) {
    unchecked { return Wrapping.wrap(Wrapping.unwrap(a) + Wrapping.unwrap(b)); }
}

type Wide is uint;
using {addWide as +} for Wide global;
function addWide(Wide a, Wide b) pure returns (Wide) { return Wide.wrap(Wide.unwrap(a) + Wide.unwrap(b)); }

contract Unavailable {}
type Excluded is uint;
using {excludedAdd as +} for Excluded global;
function excludedAdd(Excluded, Excluded) pure returns (Excluded) {
    return Excluded.wrap(type(Unavailable).creationCode.length);
}

contract OperatorAliases {
    struct Padded { bytes4 b; uint n; }
    function paddingCapture() external pure {
        bytes2[] memory bs = new bytes2[](1); bs[0] = hex"1234";
        Padded memory p = Padded(bs[0], 0);
        assert(p.b == bytes4(hex"12340000"));
    }
    function numeric() external pure {
        N a = N.wrap(6); N b = N.wrap(2);
        assert(N.unwrap(a + b) == 62);
        assert(N.unwrap(a - b) == 8);
        assert(N.unwrap(a * b) == 9);
        assert(N.unwrap(a / b) == 10);
        assert(N.unwrap(a % b) == 11);
        assert(N.unwrap(a & b) == 6);
        assert(N.unwrap(a | b) == 2);
        assert(N.unwrap(a ^ b) == 8);
    }
    function comparisons() external pure {
        N a = N.wrap(6); N b = N.wrap(2);
        assert(a == b); assert(!(a != b));
        assert(a < b); assert(a <= b);
        assert(!(a > b)); assert(!(a >= b));
        assert(!(a == a));
    }
    function unary() external pure {
        N a = N.wrap(6);
        assert(N.unwrap(-a) == 7);
        assert(N.unwrap(~a) == 9);
        Signed s = Signed.wrap(-4);
        assert(Signed.unwrap(-s) == -3);
    }
    function nominal() external pure {
        N a = N.wrap(6); N b = N.wrap(2);
        Other c = Other.wrap(6); Other d = Other.wrap(2);
        assert(N.unwrap(a + b) == 62);
        assert(Other.unwrap(c + d) == 108);
        Flag x = Flag.wrap(false); Flag y = Flag.wrap(true);
        assert(Flag.unwrap(~x)); assert(x == y);
        Bits m = Bits.wrap(hex"1200"); Bits n = Bits.wrap(hex"0203");
        assert(Bits.unwrap(m ^ n) == bytes2(hex"1203"));
        Account u = Account.wrap(address(1)); Account v = Account.wrap(address(2));
        assert(u == v);
        Payee p = Payee.wrap(payable(address(1))); Payee q = Payee.wrap(payable(address(2)));
        assert(p == q);
    }
    function order() external pure {
        uint8 i = 1;
        N a = N.wrap(i++) + N.wrap(i++);
        assert(N.unwrap(a) == 12); assert(i == 3);
        N b = -N.wrap(i++);
        assert(N.unwrap(b) == 4); assert(i == 4);
    }
    function nested() external pure {
        N a = N.wrap(1); N b = N.wrap(2); N c = N.wrap(3);
        assert(N.unwrap((a + b) + c) == 123);
        assert(N.unwrap(a + (b + c)) == 33);
    }
    function customZero() external pure {
        N a = N.wrap(6); N b = N.wrap(0);
        assert(N.unwrap(a / b) == 8);
        assert(N.unwrap(a % b) == 9);
    }
    function lazy() external pure {
        bool a = false && (N.wrap(26) == (N.wrap(26) + N.wrap(0)));
        bool b = true || (N.wrap(26) == (N.wrap(26) + N.wrap(0)));
        N c = true ? N.wrap(3) : N.wrap(26) + N.wrap(0);
        N d = false ? N.wrap(26) + N.wrap(0) : N.wrap(4);
        assert(!a); assert(b); assert(N.unwrap(c) == 3); assert(N.unwrap(d) == 4);
    }
    function wrappingBody() external pure {
        assert(Wrapping.unwrap(Wrapping.wrap(255) + Wrapping.wrap(1)) == 0);
    }
    // These are genuine failing executions, not merely unclosed proof attempts.
    function checkedBody() external pure {
        unchecked { N.wrap(26) + N.wrap(0); }
    }
    function discardedUnary() external pure { -N.wrap(255); }
    function leftRevert() internal pure returns (N) { revert(); }
    function leftPanic() internal pure returns (N) { assert(false); return N.wrap(0); }
    function failureOrderRevert() external pure { leftRevert() + leftPanic(); }
    function failureOrderPanic() external pure { leftPanic() + leftRevert(); }
    function castOrderBounds() external pure {
        Wide[] memory xs = new Wide[](0); uint d = 0;
        xs[0] + Wide.wrap(1 / d);
    }
    function castOrderDivision() external pure {
        uint[] memory xs = new uint[](0); uint d = 0;
        Flag.wrap(1 / d > 0) & Flag.wrap(uint(xs[0]) > 0);
    }
    function lengthOrderDivision() external pure {
        uint[2][] memory rows = new uint[2][](0); uint d = 0;
        Flag.wrap(1 / d > 0) & Flag.wrap(rows[0].length > 0);
    }
    function modularOrderDivision() external pure {
        uint d = 0; uint modulus = 0;
        Flag.wrap(1 / d > 0) & Flag.wrap(addmod(1, 2, modulus) > 0);
    }
    function falseBuiltin() external pure { assert(N.unwrap(N.wrap(6) + N.wrap(2)) == 8); }
    // The source classifier must follow the alias target's executed body.
    function excludedAlias() external pure { Excluded.wrap(1) + Excluded.wrap(2); }
}
