// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of `test/libsolidity/semanticTests/expressions/` and `.../exponentiation/` from the
/// solc compiler test suite. Each function names the upstream file it comes from; the upstream
/// `// f() -> v` expectation becomes an in-body `assert`, and a `return e;` becomes a bound
/// local (see `keyext.solidity.examples/solc/README.md` for the adaptation rules).
contract SolcExpressions {
    uint v;

    /// solc: expressions/inc_dec_operators.sol — `a++` yields the old value and increments.
    function postIncrementYieldsOldValue() public pure {
        uint a = 6;
        uint p = a++;
        assert(p == 6);
        assert(a == 7);
    }

    /// solc: expressions/inc_dec_operators.sol — `++a` yields the new value.
    function preIncrementYieldsNewValue() public pure {
        uint a = 6;
        uint q = ++a;
        assert(q == 7);
        assert(a == 7);
    }

    /// solc: expressions/inc_dec_operators.sol — the upstream accumulation
    /// `r = a; r += a++ * 0x10; r += ++a * 0x100` on a local, with each step bound
    /// (0x10 = 16, 0x100 = 256; the expected 6 + 6*16 + 8*256 = 2150).
    function incDecChainOnLocal() public pure {
        uint a = 6;
        uint r = a;
        uint p = a++;
        r = r + p * 16;
        uint q = ++a;
        r = r + q * 256;
        assert(a == 8);
        assert(r == 2150);
    }

    /// solc: expressions/inc_dec_operators.sol — same chain on a state variable
    /// (`v = 3; r += v++ * 0x1000; r += ++v * 0x10000`), so the storage increment rules are
    /// exercised instead of the local ones (0x1000 = 4096, 0x10000 = 65536; the expected
    /// 3*4096 + 5*65536 = 339968).
    function incDecChainOnStateVariable() public {
        v = 3;
        uint p = v++;
        uint r = p * 4096;
        uint q = ++v;
        r = r + q * 65536;
        assert(v == 5);
        assert(r == 339968);
    }

    /// solc: expressions/inc_dec_operators.sol — the decrement twins, which upstream only
    /// covers through the operator table.
    function postDecrementYieldsOldValue() public pure {
        uint a = 6;
        uint p = a--;
        assert(p == 6);
        assert(a == 5);
    }

    /// solc: expressions/inc_dec_operators.sol — `--a` yields the new value.
    function preDecrementYieldsNewValue() public pure {
        uint a = 6;
        uint q = --a;
        assert(q == 5);
        assert(a == 5);
    }

    /// solc: expressions/inc_dec_operators.sol — the upstream chain verbatim, with the
    /// compound assignment `r += a++ * 0x10` on a local instead of the bound-step rewrite
    /// used by [incDecChainOnLocal].
    function compoundAssignOnLocal() public pure {
        uint a = 6;
        uint r = a;
        r += a * 16;
        assert(r == 102);
    }

    /// solc: expressions/inc_dec_operators.sol — a bare `a++;` statement, the increment form
    /// the upstream loops use.
    function bareIncrementOnLocal() public pure {
        uint a = 6;
        a++;
        assert(a == 7);
    }

    /// solc: expressions/inc_dec_operators.sol — the same statement on a state variable.
    function bareIncrementOnStateVariable() public {
        v = 6;
        v++;
        assert(v == 7);
    }

    /// solc: expressions/conditional_expression_true_literal.sol — `true ? 5 : 10` is 5.
    function ternaryTrueLiteral() public pure {
        uint r = true ? 5 : 10;
        assert(r == 5);
    }

    /// solc: expressions/conditional_expression_false_literal.sol — `false ? 5 : 10` is 10.
    function ternaryFalseLiteral() public pure {
        uint r = false ? 5 : 10;
        assert(r == 10);
    }

    /// solc: expressions/conditional_expression_multiple.sol — the nested
    /// `x > 100 ? x > 1000 ? 1000 : 100 : x > 50 ? 50 : 10`, upstream case `f(1001) -> 1000`.
    /// @custom:key box
    function ternaryNestedOuterHigh(uint x) public pure {
        require(x == 1001);
        uint d = x > 100 ? x > 1000 ? 1000 : 100 : x > 50 ? 50 : 10;
        assert(d == 1000);
    }

    /// solc: expressions/conditional_expression_multiple.sol — upstream case `f(500) -> 100`.
    /// @custom:key box
    function ternaryNestedOuterLow(uint x) public pure {
        require(x == 500);
        uint d = x > 100 ? x > 1000 ? 1000 : 100 : x > 50 ? 50 : 10;
        assert(d == 100);
    }

    /// solc: expressions/conditional_expression_multiple.sol — upstream case `f(80) -> 50`.
    /// @custom:key box
    function ternaryNestedInnerHigh(uint x) public pure {
        require(x == 80);
        uint d = x > 100 ? x > 1000 ? 1000 : 100 : x > 50 ? 50 : 10;
        assert(d == 50);
    }

    /// solc: expressions/conditional_expression_multiple.sol — upstream case `f(40) -> 10`.
    /// @custom:key box
    function ternaryNestedInnerLow(uint x) public pure {
        require(x == 40);
        uint d = x > 100 ? x > 1000 ? 1000 : 100 : x > 50 ? 50 : 10;
        assert(d == 10);
    }

    /// solc: exponentiation/small_exp.sol — `**` is right-associative, so `2 ** 3 ** 2` is
    /// `2 ** 9`, not `8 ** 2`.
    function exponentiationIsRightAssociative() public pure {
        uint r = 2 ** 3 ** 2;
        assert(r == 512);
    }

    /// solc: exponentiation/literal_base.sol — `0 ** 0` is 1.
    function exponentiationZeroBaseZeroExponent() public pure {
        uint r = 0 ** 0;
        assert(r == 1);
    }

    /// solc: exponentiation/literal_base.sol — anything to the power 0 is 1.
    function exponentiationZeroExponent() public pure {
        uint r = 7 ** 0;
        assert(r == 1);
    }

    /// solc: exponentiation/signed_base.sol — a negative base loses its sign at an even
    /// exponent.
    /// @custom:key box
    function exponentiationSignedBaseEvenExponent(int b) public pure {
        // a negative literal directly inside the require condition does not discharge
        int minusTwo = -2;
        require(b == minusTwo);
        int even = b ** 2;
        assert(even == 4);
    }

    /// solc: exponentiation/signed_base.sol — a negative base keeps its sign at an odd
    /// exponent.
    /// @custom:key box
    function exponentiationSignedBaseOddExponent(int b) public pure {
        int minusTwo = -2;
        require(b == minusTwo);
        int odd = b ** 3;
        int expectedOdd = -8;
        assert(odd == expectedOdd);
    }
}
