// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of solc's struct and mapping tests: `semanticTests/structs/` cases not covered by
/// `SolcStructs.sol` and `SolcMappings.sol`, the mapping tests of `semanticTests/functionCall/`,
/// `variables/`, `types/`, `storage/` and `viaYul/storage/`, and `smtCheckerTests/types/struct*` and `mapping*`. Each function
/// names the upstream file it comes from (see `README.md` for the adaptation rules).
contract SolcStructsMappings {
    struct V { uint value; }
    struct PushZero { uint x; uint y; uint z; uint[3] a1; uint[] a2; }

    uint pushB;
    PushZero[] pushZero;
    uint pushA;
    V[][] va;
    V[] vb;
    struct NestedDel { uint nestedValue; mapping(uint => bool) nestedMapping; }
    struct TopDel { NestedDel nstr; uint topValue; mapping(uint => uint) topMapping; }
    struct Val { uint m_value; }
    struct Nested { uint x; uint y; }
    struct WithNested { uint a; Nested nested; uint c; }
    struct Small { uint y; uint z; }
    struct Rec { uint a; Rec[] x; }
    struct RecOnly { RecOnly[] x; }
    struct WithArrays { uint a; uint[3] b; uint[] x; }
    struct InnerL { uint x; uint y; uint z; }
    struct OuterL { uint x; InnerL s; uint[2] a; }
    struct NestedArr { uint[1] x; uint[] y; }
    struct WithArr { uint x; uint[] a; }
    struct Grid { uint[][] a; }
    struct Cube { uint[][][] a; }
    struct TA { uint y; uint[] a; }
    struct SA { uint x; TA t; uint[] a; TA[] ts; }
    struct SumArr { uint sum; uint[] a; }
    struct HoldsSum { SumArr s; uint x; }
    struct RecX { uint x; RecX[] a; }
    struct Tree { Tree[] children; }

    uint toDelete;
    TopDel str;
    Val data1;
    Val data2;
    Val data3;
    mapping(uint => WithNested) copyData;
    Small small;
    Rec rec;
    RecOnly recOnly;
    WithArrays withArrays;
    OuterL m_x;
    NestedArr src;
    NestedArr dst;
    WithArr sd;
    WithArr s1a;
    WithArr s2a;
    RecX r1;
    RecX r2;
    mapping(uint => uint) map;
    mapping(uint => mapping(uint => uint)) map2;
    mapping(uint => mapping(uint => mapping(uint => uint))) map3;
    mapping(bool => bool) boolMap;
    mapping(uint => uint) ma;
    mapping(uint => uint) mb;
    mapping(uint => mapping(uint => uint)) maps;
    mapping(uint => mapping(uint => uint)) maps8;
    mapping(uint => uint)[] severalMaps;
    mapping(uint => uint)[] severalMaps8;
    mapping(uint => uint) ia;
    mapping(uint => uint) ib;
    mapping(uint => uint)[2] fa;
    mapping(uint => uint)[2] fb;
    mapping(uint => uint) m1;
    mapping(uint => uint) m2;
    mapping(uint => uint) table;
    Tree storageTree;
    mapping(uint => uint) px;
    mapping(uint => uint)[] popMaps;
    mapping(uint => uint) simple;
    mapping(uint => mapping(uint => uint)) twodim;
    mapping(uint => uint[8]) data;
    mapping(uint => uint[]) dynamicData;

    /// solc: semanticTests/structs/delete_struct.sol
    function deleteStructKeepsNestedMappings() public {
        toDelete = 5;
        str.topValue = 1;
        str.topMapping[0] = 1;
        str.topMapping[1] = 2;
        str.nstr.nestedValue = 2;
        str.nstr.nestedMapping[0] = true;
        str.nstr.nestedMapping[1] = false;
        delete str;
        delete toDelete;
        assert(toDelete == 0);
        assert(str.topValue == 0);
        assert(str.nstr.nestedValue == 0);
        assert(str.topMapping[0] == 1);
        assert(str.topMapping[1] == 2);
        assert(str.nstr.nestedMapping[0] == true);
        assert(str.nstr.nestedMapping[1] == false);
    }

    /// solc: semanticTests/structs/struct_assign_reference_to_struct.sol
    function assignReferenceToStruct() public {
        data1.m_value = 2;
        Val storage x = data1;
        data2 = data1;
        uint retLocal = x.m_value;
        uint retGlobal = data2.m_value;
        x.m_value = 3;
        data3 = x;
        uint retGlobal3 = data3.m_value;
        uint retGlobal1 = data1.m_value;
        assert(retLocal == 2);
        assert(retGlobal == 2);
        assert(retGlobal3 == 3);
        assert(retGlobal1 == 3);
    }

    /// solc: semanticTests/structs/struct_copy.sol
    function structCopyBetweenMappingEntries() public {
        copyData[7].a = 1;
        copyData[7].nested.x = 3;
        copyData[7].nested.y = 4;
        copyData[7].c = 2;
        copyData[8] = copyData[7];
        assert(copyData[7].a == 1);
        assert(copyData[7].nested.x == 3);
        assert(copyData[7].nested.y == 4);
        assert(copyData[7].c == 2);
        assert(copyData[8].a == 1);
        assert(copyData[8].nested.x == 3);
        assert(copyData[8].nested.y == 4);
        assert(copyData[8].c == 2);
    }

    /// solc: semanticTests/structs/struct_copy.sol
    /// @custom:key box
    function structCopyFromZeroEntry() public {
        require(copyData[0].a == 0);
        require(copyData[0].nested.x == 0);
        require(copyData[0].nested.y == 0);
        require(copyData[0].c == 0);
        copyData[7].a = 1;
        copyData[7].nested.x = 3;
        copyData[7].nested.y = 4;
        copyData[7].c = 2;
        copyData[8] = copyData[7];
        copyData[7] = copyData[0];
        assert(copyData[7].a == 0);
        assert(copyData[7].nested.x == 0);
        assert(copyData[7].nested.y == 0);
        assert(copyData[7].c == 0);
        assert(copyData[8].a == 1);
        assert(copyData[8].nested.x == 3);
        assert(copyData[8].nested.y == 4);
        assert(copyData[8].c == 2);
        copyData[8] = copyData[7];
        assert(copyData[8].a == 0);
        assert(copyData[8].nested.x == 0);
        assert(copyData[8].nested.y == 0);
        assert(copyData[8].c == 0);
    }

    /// solc: semanticTests/structs/struct_delete_storage_small.sol
    function deleteSmallStruct() public {
        small.y = 1;
        small.z = 2;
        delete small;
        assert(small.y == 0);
        assert(small.z == 0);
    }

    /// solc: semanticTests/structs/struct_delete_storage_nested_small.sol
    function deleteRecursiveStruct() public {
        rec.a = 1;
        rec.x.push();
        rec.x.push();
        rec.x[0].a = 2;
        rec.x[1].a = 3;
        delete rec;
        assert(rec.a == 0);
        assert(rec.x.length == 0);
    }

    /// solc: semanticTests/structs/struct_delete_storage_with_arrays_small.sol
    function deleteStructWithFixedAndDynamicArrays() public {
        withArrays.a = 1;
        withArrays.b[0] = 2;
        withArrays.b[1] = 3;
        withArrays.x.push(4);
        withArrays.x.push(5);
        delete withArrays;
        assert(withArrays.a == 0);
        assert(withArrays.b[0] == 0);
        assert(withArrays.b[1] == 0);
        assert(withArrays.x.length == 0);
    }

    /// solc: semanticTests/structs/recursive_structs.sol
    function deleteRecursiveMemoryAndStorage() public {
        RecOnly memory s;
        s.x = new RecOnly[](10);
        delete s;
        delete recOnly;
        uint memLen = s.x.length;
        uint stLen = recOnly.x.length;
        assert(memLen == 0);
        assert(stLen == 0);
    }

    /// solc: semanticTests/structs/memory_structs_nested_load.sol
    function loadNestedStructToMemory() public {
        m_x.x = 1;
        m_x.s.x = 2;
        m_x.s.y = 3;
        m_x.s.z = 4;
        m_x.a[0] = 5;
        m_x.a[1] = 6;
        OuterL memory d = m_x;
        uint a = d.x;
        uint x = d.s.x;
        uint y = d.s.y;
        uint z = d.s.z;
        uint a1 = d.a[0];
        uint a2 = d.a[1];
        assert(a == 1);
        assert(x == 2);
        assert(y == 3);
        assert(z == 4);
        assert(a1 == 5);
        assert(a2 == 6);
    }

    /// solc: semanticTests/structs/memory_structs_nested_load.sol
    function storeNestedStructFromMemory() public {
        OuterL memory d;
        d.x = 1;
        d.s.x = 2;
        d.s.y = 3;
        d.s.z = 4;
        d.a[0] = 5;
        d.a[1] = 6;
        m_x = d;
        assert(m_x.x == 1);
        assert(m_x.s.x == 2);
        assert(m_x.s.y == 3);
        assert(m_x.s.z == 4);
        assert(m_x.a[0] == 5);
        assert(m_x.a[1] == 6);
    }

    /// solc: semanticTests/structs/copy_struct_with_nested_array_from_storage_to_storage.sol
    /// @custom:key box
    function copyStructWithNestedArrays() public {
        require(src.y.length == 0);
        src.x[0] = 3;
        src.y.push(7);
        src.y.push(11);
        dst = src;
        assert(dst.x[0] == 3);
        assert(dst.y.length == 2);
        assert(dst.y[0] == 7);
        assert(dst.y[1] == 11);
    }

    function makeStruct() internal pure returns (WithArr memory s1) {
        s1.x = 42;
        s1.a = new uint[](5);
        s1.a[2] = 43;
    }

    /// solc: smtCheckerTests/types/struct/struct_return.sol
    function structReturnedFromInternal() public pure {
        WithArr memory s2 = makeStruct();
        uint x = s2.x;
        uint a2 = s2.a[2];
        uint a3 = s2.a[3];
        assert(x == 42);
        assert(a2 == 43);
        assert(a3 != 43);
    }

    /// solc: smtCheckerTests/types/struct/struct_unary_add.sol
    /// @custom:key box
    function memoryStructIncrementAfterDelete(uint v) public pure {
        require(v <= 1000);
        WithArr memory s1;
        s1.x = v;
        delete s1;
        s1.x++;
        ++s1.x;
        uint r = s1.x;
        assert(r == 2);
    }

    /// solc: smtCheckerTests/types/struct/struct_unary_sub.sol
    /// @custom:key box
    function memoryStructDecrementAfterDelete(uint v) public pure {
        require(v <= 1000);
        WithArr memory s1;
        s1.x = v;
        delete s1;
        s1.x = 100;
        s1.x--;
        --s1.x;
        uint r = s1.x;
        assert(r == 98);
    }

    /// solc: smtCheckerTests/types/struct/struct_delete_memory.sol
    /// @custom:key box
    function memoryStructDeleteResetsArray(uint v) public pure {
        require(v <= 1000);
        WithArr memory s1;
        s1.x = v;
        s1.a = new uint[](3);
        delete s1;
        uint len = s1.a.length;
        assert(len == 0);
    }

    /// solc: smtCheckerTests/types/struct/struct_delete_storage.sol
    function storageStructDeleteResetsArray() public {
        delete sd;
        assert(sd.a.length == 0);
    }

    /// solc: smtCheckerTests/types/struct/struct_aliasing_storage.sol
    /// @custom:key box
    function storageTernaryStructAlias(uint flag) public {
        require(flag <= 1);
        bool b = flag != 0;
        WithArr storage s3 = b ? s1a : s2a;
        uint x3 = s3.x;
        uint x1 = s1a.x;
        uint x2 = s2a.x;
        assert(x3 == x1 || x3 == x2);
        s3.x = 42;
        x3 = s3.x;
        x1 = s1a.x;
        x2 = s2a.x;
        assert(x3 == x1 || x3 == x2);
    }

    /// solc: smtCheckerTests/types/struct/struct_aliasing_memory.sol
    /// @custom:key box
    function memoryTernaryStructAlias(uint flag, uint x1, uint x2) public pure {
        require(flag <= 1 && x1 <= 1000 && x2 <= 1000);
        bool b = flag != 0;
        WithArr memory s1;
        s1.x = x1;
        WithArr memory s2;
        s2.x = x2;
        WithArr memory s3 = b ? s1 : s2;
        assert(s3.x == s1.x || s3.x == s2.x);
        s3.x = 42;
        assert(s3.x == s1.x || s3.x == s2.x);
    }

    /// solc: smtCheckerTests/types/struct/struct_recursive_4.sol
    /// @custom:key box
    function recursiveStructTernaryAliases(uint flag1, uint flag2) public {
        require(flag1 <= 1 && flag2 <= 1);
        bool b1 = flag1 != 0;
        bool b2 = flag2 != 0;
        RecX storage s3 = b1 ? r1 : r2;
        RecX storage s4 = b2 ? r1 : r2;
        uint x3 = s3.x;
        uint x4 = s4.x;
        uint x1 = r1.x;
        uint x2 = r2.x;
        assert(x3 == x1 || x3 == x2);
        assert(x4 == x1 || x4 == x2);
        s3.x = 44;
        x1 = r1.x;
        x2 = r2.x;
        assert(x1 == 44 || x2 == 44);
    }

    /// solc: semanticTests/structs/conversion/recursive_storage_memory.sol
    /// @custom:key box
    function recursiveStorageToMemory() public view {
        require(storageTree.children.length == 2);
        require(storageTree.children[0].children.length == 23);
        require(storageTree.children[1].children.length == 42);
        Tree memory memoryTree;
        memoryTree = storageTree;
        uint l0 = memoryTree.children.length;
        uint l1 = memoryTree.children[0].children.length;
        uint l2 = memoryTree.children[1].children.length;
        assert(l0 == 2);
        assert(l1 == 23);
        assert(l2 == 42);
    }

    function setSumAndArray(SumArr memory m, uint v) internal pure {
        m.sum = v;
        m.a = new uint[](2);
    }

    function setNestedSumAndArray(HoldsSum memory m, uint v) internal pure {
        m.s.sum = v;
        m.s.a = new uint[](2);
    }

    /// solc: smtCheckerTests/types/struct/struct_aliasing_parameter_memory_1.sol
    /// @custom:key box
    function memoryStructParameterAliases(uint amt) public pure {
        require(amt <= 1000);
        SumArr memory s;
        setSumAndArray(s, amt);
        uint len = s.a.length;
        assert(len == 2);
    }

    /// solc: smtCheckerTests/types/struct/struct_aliasing_parameter_memory_2.sol
    /// @custom:key box
    function memoryInnerStructParameterAliases(uint amt) public pure {
        require(amt <= 1000);
        HoldsSum memory t;
        setSumAndArray(t.s, amt);
        uint len = t.s.a.length;
        assert(len == 2);
    }

    /// solc: smtCheckerTests/types/struct/struct_aliasing_parameter_memory_3.sol
    /// @custom:key box
    function memoryOuterStructParameterAliases(uint amt) public pure {
        require(amt <= 1000);
        HoldsSum memory t;
        setNestedSumAndArray(t, amt);
        uint len = t.s.a.length;
        assert(len == 2);
    }

    function combine(uint x, uint y, uint z) internal pure returns (InnerL memory s) {
        s.x = x;
        s.y = y;
        s.z = z;
    }

    function extract(InnerL memory s, uint which) internal pure returns (uint x) {
        if (which == 0) return s.x;
        else if (which == 1) return s.y;
        else return s.z;
    }

    /// solc: semanticTests/structs/memory_structs_as_function_args.sol
    function memoryStructsAsFunctionArgs() public pure {
        InnerL memory combined = combine(1, 2, 3);
        uint x = extract(combined, 0);
        uint y = extract(combined, 1);
        uint z = extract(combined, 2);
        assert(x == 1);
        assert(y == 2);
        assert(z == 3);
    }

    /// solc: smtCheckerTests/types/struct_array_branches_1d.sol
    /// @custom:key box
    function memoryStructArrayBranch1d(uint flag) public pure {
        require(flag <= 1);
        bool b = flag != 0;
        WithArr memory c;
        c.a = new uint[](2);
        c.a[0] = 0;
        if (b) c.a[0] = 1;
        else c.a[0] = 2;
        uint r = c.a[0];
        assert(r > 0);
    }

    /// solc: smtCheckerTests/types/struct_array_branches_2d.sol
    /// @custom:key box
    function memoryStructArrayBranch2d(uint flag) public pure {
        require(flag <= 1);
        bool b = flag != 0;
        Grid memory c;
        c.a = new uint[][](1);
        c.a[0] = new uint[](1);
        c.a[0][0] = 0;
        if (b) c.a[0][0] = 1;
        else c.a[0][0] = 2;
        uint r = c.a[0][0];
        assert(r > 0);
    }

    /// solc: smtCheckerTests/types/struct_array_branches_3d.sol
    function memoryStructArrayLengths3d() public pure {
        Cube memory c;
        c.a = new uint[][][](2);
        assert(c.a.length == 2);
        assert(c.a[0].length == 0);
        c.a[0] = new uint[][](2);
        assert(c.a[0].length == 2);
        assert(c.a[0][0].length == 0);
        c.a[0][0] = new uint[](2);
    }

    /// solc: smtCheckerTests/types/struct/struct_array_struct_array_memory_safe.sol
    function memoryNestedStructArrays() public pure {
        SA memory s1;
        s1.x = 2;
        assert(s1.x == 2);
        s1.t.y = 3;
        assert(s1.t.y == 3);
        s1.a = new uint[](3);
        s1.a[2] = 4;
        assert(s1.a[2] == 4);
        s1.ts = new TA[](6);
        s1.ts[3].y = 5;
        assert(s1.ts[3].y == 5);
        s1.ts[4].a = new uint[](6);
        s1.ts[4].a[5] = 6;
        assert(s1.ts[4].a[5] == 6);
    }

    /// solc: smtCheckerTests/types/struct/array_struct_array_struct_memory_safe.sol
    function memoryArrayOfNestedStructArrays() public pure {
        SA[] memory s1 = new SA[](3);
        assert(s1.length == 3);
        s1[0].x = 2;
        assert(s1[0].x == 2);
        s1[1].t.y = 3;
        assert(s1[1].t.y == 3);
        s1[2].a = new uint[](3);
        s1[2].a[2] = 4;
        assert(s1[2].a[2] == 4);
        s1[0].ts = new TA[](6);
        s1[0].ts[3].y = 5;
        assert(s1[0].ts[3].y == 5);
        s1[1].ts = new TA[](6);
        s1[1].ts[4].a = new uint[](6);
        s1[1].ts[4].a[5] = 6;
        assert(s1[1].ts[4].a[5] == 6);
    }

    /// solc: smtCheckerTests/types/mapping_1.sol
    /// @custom:key box
    function mappingWriteRead(uint x) public {
        require(x <= 1000);
        map[2] = x;
        assert(x == map[2]);
    }

    /// solc: smtCheckerTests/types/mapping_2d_1.sol
    /// @custom:key box
    function nestedMappingWriteRead(uint x) public {
        require(x <= 1000);
        x = 42;
        map2[13][14] = 42;
        assert(x == map2[13][14]);
    }

    /// solc: smtCheckerTests/types/mapping_3d_1.sol
    /// @custom:key box
    function tripleNestedMappingWriteRead(uint x) public {
        require(x <= 1000);
        x = 42;
        map3[13][14][15] = 42;
        assert(x == map3[13][14][15]);
    }

    /// solc: smtCheckerTests/types/mapping_3.sol
    function mappingOtherKeyUnchanged() public {
        map[1] = 111;
        uint x = map[2];
        map[1] = 112;
        assert(map[2] == x);
    }

    /// solc: smtCheckerTests/types/mapping_4.sol
    /// @custom:key box
    function boolMappingDefault(uint flag) public view {
        require(flag >= 1 && flag <= 1000);
        require(boolMap[true] == false);
        bool x = flag != 0;
        require(x);
        assert(x != boolMap[x]);
    }

    /// solc: smtCheckerTests/types/mapping_equal_keys_1.sol
    /// @custom:key box
    function mappingEqualKeys(uint x, uint y) public view {
        require(x <= 1000 && y <= 1000);
        require(x == y);
        assert(map[x] == map[y]);
    }

    /// solc: smtCheckerTests/types/mapping_aliasing_1.sol
    /// @custom:key box
    function mappingAliasReadsThrough(uint x) public {
        require(x <= 1000);
        ma[1] = x;
        mb[1] = x;
        ma[1] = 2;
        mapping(uint => uint) storage c = ma;
        assert(c[1] == 2);
    }

    /// solc: smtCheckerTests/types/mapping_as_local_var_1.sol
    /// @custom:key box
    function mappingTernaryLocalAlias(uint flag) public {
        require(flag <= 1);
        bool cond = flag != 0;
        mapping(uint => uint) storage a = cond ? ma : mb;
        ma[2] = 1;
        mb[2] = 2;
        a[2] = 3;
        uint a2 = a[2];
        uint x2 = ma[2];
        uint y2 = mb[2];
        if (cond) assert(a2 == x2 && a2 != y2);
        else assert(a2 == y2 && a2 != x2);
    }

    function setPx(mapping(uint => uint) storage mapParam, uint index, uint value) internal {
        mapping(uint => uint) storage map1 = mapParam;
        map1[index] = value;
    }

    /// solc: smtCheckerTests/types/mapping_as_parameter_1.sol
    /// @custom:key box
    function mappingAsParameter(uint a, uint b) public {
        require(a <= 1000 && b <= 1000);
        setPx(px, a, b);
        assert(px[a] == b);
    }

    function setInternal(mapping(uint => uint) storage mParam, uint key, uint value) internal returns (uint) {
        mapping(uint => uint) storage m = mParam;
        uint oldValue = m[key];
        m[key] = value;
        return oldValue;
    }

    /// solc: semanticTests/functionCall/mapping_internal_argument.sol
    /// @custom:key box
    function mappingAsInternalArgument() public {
        require(ia[1] == 0);
        require(ib[1] == 0);
        uint oldA = setInternal(ia, 1, 21);
        uint oldB = setInternal(ib, 1, 42);
        assert(oldA == 0);
        assert(oldB == 0);
        assert(ia[1] == 21);
        assert(ib[1] == 42);
        oldA = setInternal(ia, 1, 10);
        oldB = setInternal(ib, 1, 11);
        assert(oldA == 21);
        assert(oldB == 42);
        assert(ia[1] == 10);
        assert(ib[1] == 11);
    }

    function setInternalPair(mapping(uint => uint)[2] storage mParam, uint key, uint value1, uint value2) internal returns (uint, uint) {
        mapping(uint => uint)[2] storage m = mParam;
        uint oldValue1 = m[0][key];
        uint oldValue2 = m[1][key];
        m[0][key] = value1;
        m[1][key] = value2;
        return (oldValue1, oldValue2);
    }

    /// solc: semanticTests/functionCall/mapping_array_internal_argument.sol
    /// @custom:key box
    function fixedArrayOfMappingsAsInternalArgument() public {
        require(fa[0][1] == 0);
        require(fa[1][1] == 0);
        require(fb[0][1] == 0);
        require(fb[1][1] == 0);
        uint oldA1;
        uint oldA2;
        uint oldB1;
        uint oldB2;
        (oldA1, oldA2) = setInternalPair(fa, 1, 21, 22);
        (oldB1, oldB2) = setInternalPair(fb, 1, 42, 43);
        assert(oldA1 == 0);
        assert(oldB2 == 0);
        assert(fa[0][1] == 21);
        assert(fa[1][1] == 22);
        assert(fb[0][1] == 42);
        assert(fb[1][1] == 43);
        (oldA1, oldA2) = setInternalPair(fa, 1, 10, 30);
        assert(oldA1 == 21);
        assert(oldA2 == 22);
        assert(fa[0][1] == 10);
        assert(fa[1][1] == 30);
    }

    function pickMapping() internal returns (mapping(uint => uint) storage r) {
        r = m1;
        mapping(uint => uint) storage first = r;
        first[1] = 42;
        r = m2;
        mapping(uint => uint) storage second = r;
        second[1] = 84;
    }

    /// solc: semanticTests/functionCall/mapping_internal_return.sol
    /// @custom:key box
    function mappingReturnedFromInternal() public {
        require(m1[0] == 0);
        require(m1[2] == 0);
        require(m2[0] == 0);
        mapping(uint => uint) storage m = pickMapping();
        m[2] = 17;
        assert(m1[0] == 0);
        assert(m1[1] == 42);
        assert(m1[2] == 0);
        assert(m2[0] == 0);
        assert(m2[1] == 84);
        assert(m2[2] == 17);
    }

    /// solc: semanticTests/variables/mapping_local_assignment.sol
    /// @custom:key box
    function mappingLocalReassignment() public {
        require(m1[2] == 0);
        require(m2[1] == 0);
        mapping(uint => uint) storage m = m1;
        m[1] = 42;
        m = m2;
        m[2] = 21;
        assert(m1[1] == 42);
        assert(m1[2] == 0);
        assert(m2[1] == 0);
        assert(m2[2] == 21);
    }

    /// solc: semanticTests/variables/mapping_local_tuple_assignment.sol
    /// @custom:key box
    function mappingLocalTupleReassignment() public {
        require(m1[2] == 0);
        require(m2[1] == 0);
        mapping(uint => uint) storage m = m1;
        m[1] = 42;
        uint v;
        (m, v) = (m2, 21);
        m[2] = v;
        assert(m1[1] == 42);
        assert(m1[2] == 0);
        assert(m2[1] == 0);
        assert(m2[2] == 21);
    }

    /// solc: semanticTests/types/mapping_simple.sol
    /// @custom:key box
    function mappingSetGetSequence() public {
        require(table[0] == 0);
        require(table[1] == 0);
        require(table[167] == 0);
        assert(table[0] == 0);
        assert(table[1] == 0);
        table[1] = 161;
        assert(table[0] == 0);
        assert(table[1] == 161);
        assert(table[167] == 0);
        table[0] = 239;
        assert(table[0] == 239);
        assert(table[1] == 161);
        table[1] = 5;
        assert(table[0] == 239);
        assert(table[1] == 5);
        assert(table[167] == 0);
    }

    /// solc: semanticTests/storage/mappings_array_pop_delete.sol
    /// @custom:key box
    function mappingsSurvivePopAndDelete() public {
        require(popMaps.length == 0);
        popMaps.push();
        popMaps[popMaps.length - 1][42] = 64;
        uint v1 = popMaps[popMaps.length - 1][42];
        assert(v1 == 64);
        popMaps.pop();
        popMaps.push();
        uint v2 = popMaps[popMaps.length - 1][42];
        assert(v2 == 64);
        delete popMaps;
        uint len = popMaps.length;
        assert(len == 0);
        popMaps.push();
        uint v3 = popMaps[popMaps.length - 1][42];
        assert(v3 == 64);
    }

    /// solc: semanticTests/viaYul/storage/mappings.sol
    /// @custom:key box
    function mappingComputedKeys(uint off) public {
        require(off < 3);
        simple[off + 2] = 3;
        simple[off + 3] = 4;
        simple[115792089237316195423570985008687907853269984665640564039457584007913129639935] = 5;
        uint c = simple[115792089237316195423570985008687907853269984665640564039457584007913129639935];
        uint b = simple[3 + off];
        uint a = simple[2 + off];
        assert(a == 3);
        assert(b == 4);
        assert(c == 5);
    }

    /// solc: semanticTests/viaYul/storage/mappings.sol
    /// @custom:key box
    function twoDimMappingTransposedKey() public {
        require(twodim[3][2] == 0);
        twodim[2][3] = 3;
        uint a = twodim[3][2];
        uint b = twodim[2][3];
        assert(a == 0);
        assert(b == 3);
    }

    /// solc: semanticTests/storage/accessors_mapping_for_array.sol
    /// @custom:key box
    function mappingOfArrays() public {
        require(dynamicData[2].length == 0);
        data[2][2] = 8;
        for (uint i = 0; i < 3; i++)
            dynamicData[2].push();
        dynamicData[2][2] = 8;
        uint d = data[2][2];
        uint len = dynamicData[2].length;
        uint e = dynamicData[2][2];
        assert(d == 8);
        assert(len == 3);
        assert(e == 8);
    }

    function writeTwoMappings(mapping(uint => uint) storage map1Param, mapping(uint => uint) storage mapBParam) internal {
        mapping(uint => uint) storage map1 = map1Param;
        mapping(uint => uint) storage mapB = mapBParam;
        map1[0] = 2;
        ma[0] = 42;
        maps[0][0] = 42;
        maps8[0][0] = 42;
        mapB[0] = 1;
        assert(maps8[0][0] == 42);
        assert(mapB[0] == 1);
    }

    /// solc: smtCheckerTests/types/mapping_aliasing_2.sol
    /// @custom:key box
    function mappingParametersMayAlias(uint flag, uint x, uint y) public {
        require(flag <= 1 && x <= 1000 && y <= 1000);
        bool b = flag != 0;
        if (b) writeTwoMappings(ma, maps[y]);
        else writeTwoMappings(maps[x], maps[y]);
    }

    function writeMappingElement(mapping(uint => uint) storage mParam) internal {
        mapping(uint => uint) storage m = mParam;
        require(severalMaps.length > 0);
        require(severalMaps8.length > 0);
        severalMaps[0][0] = 42;
        severalMaps8[0][0] = 42;
        m[0] = 2;
        assert(severalMaps8[0][0] == 42);
    }

    /// solc: smtCheckerTests/types/array_mapping_aliasing_1.sol
    /// @custom:key box
    function arrayOfMappingsElementAlias(uint x) public {
        require(x <= 1000);
        require(x < severalMaps.length);
        writeMappingElement(severalMaps[x]);
    }

    /// solc: semanticTests/structs/struct_storage_push_zero_value.sol
    /// @custom:key box
    function pushedStructIsZero() public {
        require(pushZero.length == 0);
        pushB = 23;
        pushA = 17;
        pushZero.push();
        assert(pushZero[0].x == 0);
        assert(pushZero[0].y == 0);
        assert(pushZero[0].z == 0);
        assert(pushZero[0].a1[0] == 0);
        assert(pushZero[0].a1[1] == 0);
        assert(pushZero[0].a1[2] == 0);
        assert(pushZero[0].a2.length == 0);
        assert(pushB == 23);
        assert(pushA == 17);
    }

    /// solc: semanticTests/structs/copy_struct_array_from_storage.sol
    /// @custom:key box
    function copyStructArrayIntoNestedArray() public {
        require(va.length == 0);
        require(vb.length == 0);
        va.push();
        va[0].push();
        va[0][0].value = 1;
        va[0].push();
        va[0][1].value = 2;
        va[0].push();
        va[0][2].value = 3;
        vb.push();
        vb[0].value = 4;
        vb.push();
        vb[1].value = 5;
        vb.push();
        vb[2].value = 6;
        vb.push();
        vb[3].value = 7;
        va.push();
        va[1] = vb;
        assert(va.length == 2);
        assert(va[0].length == 3);
        assert(va[1].length == 4);
        assert(va[1][0].value == 4);
        assert(va[1][1].value == 5);
        assert(va[1][2].value == 6);
        assert(va[1][3].value == 7);
    }

    /// solc: semanticTests/structs/copy_struct_array_from_storage.sol
    /// @custom:key box
    function copyStructArraysIntoMemoryRows() public {
        require(va.length == 1);
        require(va[0].length == 3);
        require(vb.length == 4);
        vb[0].value = 4;
        vb[1].value = 5;
        vb[2].value = 6;
        vb[3].value = 7;
        V[][] memory temp = new V[][](2);
        temp[0] = va[0];
        temp[1] = vb;
        assert(temp.length == 2);
        assert(temp[0].length == 3);
        assert(temp[1].length == 4);
        assert(temp[1][0].value == 4);
        assert(temp[1][3].value == 7);
    }

}
