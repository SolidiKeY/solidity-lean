// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SolcConstructorsOpen {
    enum Choice { GoLeft, GoRight, GoStraight, Sit }

    struct D {
        uint p;
        bool q;
    }

    uint constant X = 56;
    Choice constant CHOICES = Choice.GoLeft;
    uint immutable atDecl = 2;
    int immutable immX = 1;
    int immutable immY = 3;
    uint immutable delA;
    uint immutable delB = 0x42;
    uint delC;
    uint ci = 1;
    uint ck = 2;
    uint dw;
    int ds;
    bool dflag;
    address dad;
    uint[] darr;
    mapping(uint => uint) dm;
    Choice dchoice;
    D dst;
    uint immutable u;
    bool immutable b;
    address immutable a;
    uint m_a;
    uint ix;
    uint iy;
    mapping(uint => uint) m1;
    mapping(uint => uint) m2;

    /// solc: semanticTests/constructor/state_variable_initialization.sol, semanticTests/immutable/{assign_at_declaration,increment_decrement,delete}.sol, semanticTests/constants/{simple_constant_variables_test,constant_variables}.sol, smtCheckerTests/deployment/deploy_trusted_keep_storage_constraints.sol
    // open: closes in KeY, but SolidityRuntimeCheck skips a contract with a constructor or an initialized state variable, so no EVM cross-check
    constructor() {
        ci = ci + ci;
        ck = ck - ci;
        immX--;
        --immX;
        immY++;
        ++immY;
        --immY;
        delete delA;
        delete delB;
        delC = delB * 2 + delA;
        uint ri = ci;
        uint rk = ck;
        assert(ri == 2);
        assert(rk == 0);
        uint ra = atDecl;
        assert(ra == 2);
        int rx = immX;
        int ry = immY;
        int expected = -1;
        assert(rx == expected);
        assert(ry == 4);
        uint da = delA;
        uint db = delB;
        uint dc = delC;
        assert(da == 0);
        assert(db == 0);
        assert(dc == 0);
        uint cx = X;
        Choice cc = CHOICES;
        assert(cx == 56);
        assert(cc == Choice.GoLeft);
        uint rw = dw;
        int rs = ds;
        bool rf = dflag;
        address rad = dad;
        uint rl = darr.length;
        uint rm = dm[5];
        Choice rch = dchoice;
        uint rp = dst.p;
        bool rq = dst.q;
        assert(rw == 0);
        assert(rs == 0);
        assert(rf == false);
        assert(rad == address(0));
        assert(rl == 0);
        assert(rm == 0);
        assert(rch == Choice.GoLeft);
        assert(rp == 0);
        assert(rq == false);
    }

    function value() internal view returns (uint) {
        return msg.value;
    }

    /// solc: semanticTests/immutable/uninitialized.sol
    // open: an immutable is plain storage, so outside the constructor a never-assigned one is unconstrained instead of zero
    function immutableUninitialized() public view {
        uint ru = u;
        bool rb = b;
        address ra = a;
        assert(ru == 0);
        assert(rb == false);
        assert(ra == address(0));
    }

    /// solc: semanticTests/variables/delete_local.sol
    // open: no rule for delete on a local variable
    function deleteLocal() public pure {
        uint v = 5;
        delete v;
        uint res = v;
        assert(res == 0);
    }

    /// solc: semanticTests/variables/delete_locals.sol
    // open: no rule for delete on a local variable
    function deleteLocals() public pure {
        uint v = 5;
        uint w2 = 6;
        uint x = 7;
        delete v;
        uint res1 = w2;
        uint res2 = x;
        assert(res1 == 6);
        assert(res2 == 7);
    }

    /// solc: semanticTests/state/msg_value.sol
    // open: a non-payable function does not assume msg.value == 0
    function msgValueZero() public view {
        uint v = value();
        assert(v == 0);
    }

    /// solc: semanticTests/immutable/multiple_initializations.sol
    // open: no rule for a compound assignment used as an expression
    /// @custom:key box
    function multipleInitializationsAssignExpr() public {
        require(ix == 0);
        ix = ix + 1;
        iy = ix += 2;
        uint r = ix;
        uint s = iy;
        assert(r == 3);
        assert(s == 3);
    }

    /// solc: semanticTests/variables/mapping_local_compound_assignment.sol
    // open: a parenthesized assignment as index base, (m = m2)[2] = 21, gets stuck
    /// @custom:key box
    function mappingLocalCompoundAssignment() public {
        require(m1[2] == 0 && m2[1] == 0);
        mapping(uint => uint) storage m = m1;
        m[1] = 42;
        (m = m2)[2] = 21;
        uint ra = m1[1];
        uint rb = m1[2];
        uint rc = m2[1];
        uint rd = m2[2];
        assert(ra == 42);
        assert(rb == 0);
        assert(rc == 0);
        assert(rd == 21);
    }

    /// solc: semanticTests/constructor/base_constructor_arguments.sol
    // open: the right side of a compound assignment reads storage
    function baseConstructorArgumentsSelfMul() public {
        m_a = 7;
        m_a *= m_a;
        uint r = m_a;
        assert(r == 49);
    }
}
