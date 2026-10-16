// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of semanticTests/{enums,literals,types} and smtCheckerTests/{types,typecast}.
contract SolcTypes {
    enum ActionChoices { GoLeft, GoRight, GoStraight, Sit }
    enum Direction { A, B, Left, Right }
    enum E3 { A, B, C }
    enum Choice { A, B, C }
    enum D { Left, Right }
    enum E { Left, Right }
    enum E256 {
        E000, E001, E002, E003, E004, E005, E006, E007, E008, E009,
        E010, E011, E012, E013, E014, E015, E016, E017, E018, E019,
        E020, E021, E022, E023, E024, E025, E026, E027, E028, E029,
        E030, E031, E032, E033, E034, E035, E036, E037, E038, E039,
        E040, E041, E042, E043, E044, E045, E046, E047, E048, E049,
        E050, E051, E052, E053, E054, E055, E056, E057, E058, E059,
        E060, E061, E062, E063, E064, E065, E066, E067, E068, E069,
        E070, E071, E072, E073, E074, E075, E076, E077, E078, E079,
        E080, E081, E082, E083, E084, E085, E086, E087, E088, E089,
        E090, E091, E092, E093, E094, E095, E096, E097, E098, E099,
        E100, E101, E102, E103, E104, E105, E106, E107, E108, E109,
        E110, E111, E112, E113, E114, E115, E116, E117, E118, E119,
        E120, E121, E122, E123, E124, E125, E126, E127, E128, E129,
        E130, E131, E132, E133, E134, E135, E136, E137, E138, E139,
        E140, E141, E142, E143, E144, E145, E146, E147, E148, E149,
        E150, E151, E152, E153, E154, E155, E156, E157, E158, E159,
        E160, E161, E162, E163, E164, E165, E166, E167, E168, E169,
        E170, E171, E172, E173, E174, E175, E176, E177, E178, E179,
        E180, E181, E182, E183, E184, E185, E186, E187, E188, E189,
        E190, E191, E192, E193, E194, E195, E196, E197, E198, E199,
        E200, E201, E202, E203, E204, E205, E206, E207, E208, E209,
        E210, E211, E212, E213, E214, E215, E216, E217, E218, E219,
        E220, E221, E222, E223, E224, E225, E226, E227, E228, E229,
        E230, E231, E232, E233, E234, E235, E236, E237, E238, E239,
        E240, E241, E242, E243, E244, E245, E246, E247, E248, E249,
        E250, E251, E252, E253, E254, E255
    }
    struct SD { uint x; D d; }

    uint constant X = 1 ether + 1 gwei + 1 wei;

    ActionChoices choices;
    mapping(E3 => uint8) table;
    uint g;
    uint e;
    uint m;
    uint h;
    uint dd;
    uint w;
    D d;
    address a;
    bool b;

    function dirRight() internal pure returns (Direction) {
        return Direction.Right;
    }

    function tripleOf() internal pure returns (uint, bool, uint) {
        uint x = 3;
        bool bb = true;
        uint y = 999;
        return (x, bb, y);
    }

    function pairOf() internal pure returns (uint, uint) {
        return (2, 3);
    }

    /// solc: semanticTests/enums/using_enums.sol
    function usingEnums() public {
        choices = ActionChoices.GoStraight;
        uint r = uint256(choices);
        assert(r == 2);
    }

    /// solc: semanticTests/enums/enum_referencing.sol
    function enumReferencing() public pure {
        Direction dr = dirRight();
        uint r = uint(dr);
        assert(r == 3);
    }

    /// solc: semanticTests/enums/enum_with_256_members.sol
    function enumWith256Members() public pure {
        uint lo = uint(E256.E000);
        uint hi = uint8(E256.E255);
        assert(lo == 0);
        assert(hi == 255);
    }

    /// solc: semanticTests/types/mapping_enum_key_v1.sol
    /// @custom:key box
    function mappingEnumKey() public {
        require(table[E3.C] == 0);
        table[E3.B] = 0xa1;
        table[E3.A] = 0xef;
        table[E3.B] = 0x05;
        uint8 ra = table[E3.A];
        uint8 rb = table[E3.B];
        uint8 rc = table[E3.C];
        assert(ra == 0xef);
        assert(rb == 0x05);
        assert(rc == 0);
    }

    /// solc: semanticTests/types/nested_tuples.sol
    function nestedTuplesTrailingWildcard() public pure {
        int x;
        (x, ) = (4, (8, 16, 32));
        assert(x == 4);
    }

    /// solc: semanticTests/literals/denominations.sol
    function denominations() public pure {
        uint r = 1 ether + 1 gwei + 1 wei;
        assert(r == 1000000001000000001);
    }

    /// solc: semanticTests/literals/ether.sol
    function etherDenomination() public pure {
        uint r = 1 ether;
        assert(r == 1000000000000000000);
    }

    /// solc: semanticTests/literals/gwei.sol
    function gweiDenomination() public pure {
        uint r = 1 gwei;
        assert(r == 1000000000);
    }

    /// solc: semanticTests/literals/wei.sol
    function weiDenomination() public pure {
        uint r = 1 wei;
        assert(r == 1);
    }

    /// solc: semanticTests/literals/fractional_denominations.sol
    function fractionalDenominations() public {
        g = 1.5 gwei;
        e = 1.5 ether;
        m = 1.5 minutes;
        h = 1.5 hours;
        dd = 1.5 days;
        w = 1.5 weeks;
        uint rg = g;
        uint re = e;
        uint rm = m;
        uint rh = h;
        uint rd = dd;
        uint rw = w;
        assert(rg == 1500000000);
        assert(re == 1500000000000000000);
        assert(rm == 90);
        assert(rh == 5400);
        assert(rd == 129600);
        assert(rw == 907200);
    }

    /// solc: semanticTests/literals/scientific_notation.sol
    function scientificNotation() public pure {
        uint f = 2e10 wei;
        uint gg = 200e-2 wei;
        uint hh = 2.5e1;
        int i = -2e10;
        int j = -200e-2;
        int k = -2.5e1;
        int ei = -20000000000;
        int ej = -2;
        int ek = -25;
        assert(f == 20000000000);
        assert(gg == 2);
        assert(hh == 25);
        assert(i == ei);
        assert(j == ej);
        assert(k == ek);
    }

    /// solc: smtCheckerTests/types/bool_int_mixed_1.sol
    /// @custom:key box
    function boolIntMixed1(uint px) public pure {
        require(px <= 1);
        bool x = px == 1;
        uint v;
        if (x) v = 1;
        assert(!x || v > 0);
    }

    /// solc: smtCheckerTests/types/bool_int_mixed_2.sol
    /// @custom:key box
    function boolIntMixed2(uint px, uint v) public pure {
        require(px <= 1 && v <= 1000);
        bool x = px == 1;
        require(!x || v > 0);
        uint u = v;
        assert(!x || u > 0);
    }

    /// solc: smtCheckerTests/types/bool_int_mixed_3.sol
    /// @custom:key box
    function boolIntMixed3(uint px, uint py) public pure {
        require(px <= 1 && py <= 1);
        bool x = px == 1;
        bool y = py == 1;
        uint v;
        if (x) {
            if (y) {
                v = 0;
            } else {
                v = 1;
            }
        } else {
            if (y) {
                v = 1;
            } else {
                v = 0;
            }
        }
        bool xorXY = (x && !y) || (!x && y);
        assert(!xorXY || v > 0);
    }

    /// solc: smtCheckerTests/types/bool_simple_3.sol
    /// @custom:key box
    function boolSimple3(uint px, uint py) public pure {
        require(px <= 1 && py <= 1);
        bool x = px == 1;
        bool y = py == 1;
        bool z = x || y;
        assert(!(x && y) || z);
    }

    /// solc: smtCheckerTests/types/bool_simple_4.sol
    /// @custom:key box
    function boolSimple4(uint px) public pure {
        require(px <= 1);
        bool x = px == 1;
        if (x) {
            assert(x);
        } else {
            assert(!x);
        }
    }

    /// solc: smtCheckerTests/types/bool_simple_5.sol
    /// @custom:key box
    function boolSimple5(uint px) public pure {
        require(px <= 1);
        bool x = px == 1;
        bool y = x;
        assert(x == y);
    }

    /// solc: smtCheckerTests/types/bool_simple_6.sol
    /// @custom:key box
    function boolSimple6(uint px) public pure {
        require(px <= 1);
        bool x = px == 1;
        require(x);
        bool y;
        y = false;
        assert(x || y);
    }

    /// solc: smtCheckerTests/types/enum_explicit_values.sol
    /// @custom:key box
    function enumExplicitValues(D p) public {
        require(p == D.Left);
        d = D.Right;
        assert(d != p);
    }

    /// solc: smtCheckerTests/types/enum_in_struct.sol
    function enumInStruct() public pure {
        SD memory s;
        s.d = D.Left;
        D r = s.d;
        assert(r == D.Left);
    }

    /// solc: smtCheckerTests/types/enum_transitivity.sol
    /// @custom:key box
    function enumTransitivity(D p, D q) public view {
        require(p == q && d == p);
        assert(d == q);
    }

    /// solc: smtCheckerTests/types/enum_in_library.sol
    function enumParamReassigned(E p) public pure {
        p = E.Left;
        assert(p == E.Left);
    }

    /// solc: smtCheckerTests/types/storage_value_vars_3.sol
    /// @custom:key box
    function storageValueVars3(uint x) public {
        require(x <= 1);
        if (x == 0) {
            a = 0x0000000000000000000000000000000000000100;
            b = true;
        } else {
            a = 0x0000000000000000000000000000000000000200;
            b = false;
        }
        assert(b == (a < 0x0000000000000000000000000000000000000200));
    }

    /// solc: smtCheckerTests/types/rational_large_1.sol
    function rationalLarge() public pure {
        uint x = 8e130 % 9;
        assert(x == 8);
    }

    /// solc: smtCheckerTests/types/tuple_assignment.sol
    function tupleAssignment() public pure {
        uint x;
        uint y;
        (x, y) = (2, 4);
        assert(x == 2);
        assert(y == 4);
    }

    /// solc: smtCheckerTests/types/tuple_assignment_compound.sol
    function tupleAssignmentCompound() public pure {
        uint p = 1;
        uint q = 3;
        p += ((((q))));
        assert(p != 3);
    }

    /// solc: smtCheckerTests/types/tuple_declarations.sol
    function tupleDeclarations() public pure {
        (uint x, uint y) = (2, 4);
        assert(x == 2);
        assert(y == 4);
    }

    /// solc: smtCheckerTests/types/tuple_declarations_function.sol
    function tupleDeclarationsFunction() public pure {
        (uint x, bool bb, uint y) = tripleOf();
        assert(x == 3);
        assert(bb);
        assert(y == 999);
    }

    /// solc: smtCheckerTests/types/tuple_function_2.sol
    function tupleFunctionWildcard() public pure {
        uint x;
        (x, ) = pairOf();
        assert(x == 2);
    }

    /// solc: smtCheckerTests/types/tuple_1_chain_1.sol
    function tupleSingleElementChain() public pure {
        uint r;
        if (0 == 0)
            (r) = 13;
        assert(r == 13);
    }

    /// solc: smtCheckerTests/typecast/address_literal.sol
    function addressLiteral() public pure {
        address p = address(0);
        address c = address(0);
        address q = p;
        address r = address(0x12345678);
        assert(c == q);
        assert(p == c);
        assert(r == address(305419896));
    }

    /// solc: smtCheckerTests/typecast/cast_address_1.sol
    /// @custom:key box
    function castAddress(uint160 v) public pure {
        require(v >= 1);
        address p = address(v);
        require(p != address(0));
        assert(p != address(0));
    }

    /// solc: smtCheckerTests/typecast/cast_larger_2.sol
    function castLarger() public pure {
        uint16 p = 0x1234;
        uint32 q = uint32(p);
        assert(p == q);
    }

    /// solc: smtCheckerTests/typecast/downcast.sol
    function downcastSignedPreserving() public pure {
        int8 z = int8(-1);
        int8 m1 = -1;
        int8 m2 = -2;
        assert(z == m1);
        z = int8(int(0) - 1);
        assert(z == m1);
        z = int8(int(0) - 2);
        assert(z == m2);
    }

    /// solc: smtCheckerTests/typecast/number_literal.sol
    function numberLiteral() public pure {
        uint x = 1234;
        uint y = 0;
        assert(x != y);
        assert(x == uint(1234));
        assert(y == uint(0));
    }

    /// solc: smtCheckerTests/typecast/same_size.sol
    function sameSizePreserving() public pure {
        int8 p = -10;
        int8 y = int8(p);
        int8 ten = -10;
        assert(y == ten);
        uint8 x = uint8(int8(100));
        uint16 v = uint16(int16(200));
        assert(x == 100);
        assert(v == 200);
        address c = address(0);
        uint160 cv = uint160(c);
        assert(cv == 0);
        assert(c == address(uint160(0)));
    }

    /// solc: smtCheckerTests/typecast/upcast.sol
    function upcastPreserving() public pure {
        int z = int(int8(-1));
        int m1 = -1;
        assert(z == m1);
        z = int(int16(5000));
        assert(z == 5000);
        uint x = uint(uint16(5000));
        assert(x == 5000);
        address p = address(uint160(uint8(0)));
        assert(p == address(0));
    }

    /// solc: semanticTests/enums/using_contract_enums_with_explicit_contract_name.sol
    function enumExplicitContractName() public pure {
        SolcTypes.Choice r = SolcTypes.Choice.B;
        uint v = uint(r);
        assert(v == 1);
    }

    /// solc: semanticTests/literals/denominations.sol
    function denominationsConstant() public pure {
        uint r = X;
        assert(r == 1000000001000000001);
    }
}
