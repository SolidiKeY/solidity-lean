// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of solc's array tests not covered by `SolcArrays.sol` and `SolcMemory.sol`:
/// `semanticTests/array/` (push, pop, delete, copying, memory allocation), `semanticTests/storage/`,
/// and `smtCheckerTests/array_members/` and `out_of_bounds/`. Each function names the upstream file
/// it comes from (see `README.md` for the adaptation rules).
contract SolcArrayMembers {
    uint[][] lhs2d;
    uint[][][] lhs3d;
    uint[][] lenArr;
    uint[][] lenArr2;
    struct S { uint x; }
    struct B { int[] b; }
    struct TS { B[] s; }
    struct Data { uint x; uint y; }
    struct St { uint a; uint[] finalArray; }
    struct SA { uint[][] arr; }
    struct T { B s; }
    struct PS { uint a; uint b; uint[3] c; uint[] d; }

    uint[] popData;
    uint[] pushData;
    uint[] popEmpty;
    int[] parenData;
    uint[] noArgs1d;
    uint[] lhsRhs1d;
    S[] noArgsStruct;
    uint[] deleted;
    uint[] cleared;
    uint[] fromMemory;
    uint[][] nestedFromMem;
    uint[][] nestedFromMemory;
    int[] compound;
    B sb;
    T tsb;
    uint[][] push2dArg;
    PS[] structData;
    uint[] pushArg;
    uint[] zero1d;
    int[][] pushPush2;
    int[][][] pushPush3;
    uint[] lhs1d;
    uint[] lhs1dLast;
    B sb2;
    TS tsb2;
    uint[][] refAlias;
    uint[][] refAlias2;
    uint[][] pop2d;
    uint[] popLoop;
    uint[] overflow;
    uint[] overflow2;
    uint[] lenA;
    uint[] lenB;
    uint[] lenC;
    uint[] lenD;
    mapping(uint => uint[]) lenMap;
    mapping(uint => uint[][]) lenMap2d;
    uint[] addrLike;
    Data[1024] fixedData;
    uint[1027] ids;
    uint[5][] nestedFixed;
    mapping(uint => uint[][]) arrMap;
    uint[][] arrMapSrc;
    uint[] dynA;
    uint[3] fixedB;
    mapping(uint => uint)[][] map2d;
    mapping(uint => uint)[][] map2dPop;
    uint[][] same3;
    uint[][] same2;
    uint[][] same4;
    uint[] sameMem;
    uint[][] nestedP;
    uint[] dyn1;
    uint[] dyn2;
    uint[] dynamicData;
    uint[] smallTypeData;
    uint[9] staticData1;
    uint[] staticData2;
    uint[40] big;
    uint[20] small;
    mapping(uint => mapping(uint => St[5])) multipleMap;
    uint[][][] src1;
    uint[][] dst1;
    uint[][] zero2d;
    uint[][] nestedToMemory;
    SA s1;
    SA s2;
    uint[] fnArr;
    int[][] pointer2d;

    function emptyMemory() internal pure returns (uint[] memory) {
    }

    function threeRows() internal returns (int[] storage) {
        pointer2d.push();
        pointer2d.push();
        pointer2d.push();
        return pointer2d[2];
    }

    /// solc: semanticTests/array/arrayMemoryAllocation/array_zeroed_memory_index_access.sol
    /// @custom:key box
    function memoryArrayZeroed(uint n, uint a) public pure {
        require(n == 5 && a == 4);
        uint[] memory x = new uint[](n);
        uint r = x[a];
        assert(r == 0);
    }

    /// solc: semanticTests/array/arrayMemoryAllocation/array_2d_zeroed_memory_index_access.sol
    /// @custom:key box
    function memory2dZeroed(uint n, uint m, uint a, uint b) public pure {
        require(n == 2 && m == 4 && a == 1 && b == 3);
        uint[][] memory x = new uint[][](n);
        for (uint i = 0; i < n; ++i)
            x[i] = new uint[](m);
        uint r = x[a][b];
        assert(r == 0);
    }

    /// solc: semanticTests/array/arrayMemoryAllocation/array_static_zeroed_memory_index_access.sol
    function memoryStaticZeroed() public pure {
        uint[3] memory x;
        uint r = x[2];
        assert(r == 0);
    }

    /// solc: semanticTests/array/arrayMemoryAllocation/array_array_static.sol
    /// @custom:key box
    function memoryArrayOfStaticZeroed(uint n, uint m) public pure {
        require(n == 2 && m == 1);
        uint[4][] memory x = new uint[4][](n);
        uint r = x[m][0];
        assert(r == 0);
    }

    /// solc: semanticTests/array/array_memory_create.sol
    /// @custom:key box
    function memoryCreateLength(uint len) public pure {
        require(len == 7);
        uint[] memory array = new uint[](len);
        uint r = array.length;
        assert(r == len);
    }

    /// solc: semanticTests/array/create_dynamic_array_with_zero_length.sol
    function memoryZeroLength2d() public pure {
        uint[][] memory a = new uint[][](0);
        uint r = a.length;
        assert(r == 0);
    }

    /// solc: semanticTests/array/create_multiple_dynamic_arrays.sol
    function memoryMultipleDynamic() public pure {
        uint[][] memory x = new uint[][](42);
        assert(x[0].length == 0);
        x[0] = new uint[](1);
        x[0][0] = 1;
        assert(x[4].length == 0);
        x[4] = new uint[](1);
        x[4][0] = 2;
        assert(x[10].length == 0);
        x[10] = new uint[](1);
        x[10][0] = 44;
        uint[][] memory y = new uint[][](24);
        assert(y[0].length == 0);
        y[0] = new uint[](1);
        y[0][0] = 1;
        assert(y[4].length == 0);
        y[4] = new uint[](1);
        y[4][0] = 2;
        assert(y[10].length == 0);
        y[10] = new uint[](1);
        y[10][0] = 88;
        uint x0 = x[0][0];
        uint y0 = y[0][0];
        uint x4 = x[4][0];
        uint y4 = y[4][0];
        uint x10 = x[10][0];
        uint y10 = y[10][0];
        assert(x0 == y0);
        assert(x4 == y4);
        assert(x10 == 44);
        assert(y10 == 88);
    }

    /// solc: semanticTests/array/create_memory_array.sol
    function memoryArrayOfFixed() public pure {
        uint[2][] memory y = new uint[2][](300);
        y[203][1] = 8;
        uint r = y[203][1];
        assert(r == 8);
    }

    /// solc: semanticTests/array/delete/delete_memory_array.sol
    function deleteMemoryArray() public pure {
        uint[] memory data = new uint[](2);
        data[0] = 234;
        data[1] = 123;
        delete data;
        uint r = data.length;
        assert(r == 0);
    }

    /// solc: semanticTests/array/pop/array_pop.sol
    /// @custom:key box
    function popTracksLength() public {
        require(popData.length == 0);
        popData.push(7);
        popData.push(3);
        popData.pop();
        uint x = popData.length;
        popData.pop();
        uint l = popData.length;
        assert(x == 1);
        assert(l == 0);
    }

    /// solc: semanticTests/array/push/array_push.sol
    /// @custom:key box
    function pushReadsBack() public {
        require(pushData.length == 0);
        pushData.push(5);
        uint x = pushData[0];
        pushData.push(4);
        uint y = pushData[1];
        pushData.push(3);
        uint l = pushData.length;
        uint z = pushData[2];
        assert(x == 5);
        assert(y == 4);
        assert(z == 3);
        assert(l == 3);
    }

    /// solc: semanticTests/array/pop/array_pop_storage_empty.sol
    /// @custom:key box
    function pushPopLeavesEmpty() public {
        require(popEmpty.length == 0);
        popEmpty.push(7);
        popEmpty.pop();
        uint l = popEmpty.length;
        assert(l == 0);
    }

    /// solc: semanticTests/array/pop/parenthesized.sol
    /// @custom:key box
    function parenthesizedPop() public {
        require(parenData.length == 0);
        parenData.push(1);
        (parenData.pop)();
        uint l = parenData.length;
        assert(l == 0);
    }

    /// solc: semanticTests/array/push/push_no_args_1d.sol
    /// @custom:key box
    function pushNoArgs1dLvalue() public {
        require(noArgs1d.length == 0);
        noArgs1d.push() = 42;
        assert(noArgs1d.length == 1);
        assert(noArgs1d[0] == 42);
        noArgs1d.push();
        assert(noArgs1d.length == 2);
        assert(noArgs1d[1] == 0);
        noArgs1d.push() = 111;
        assert(noArgs1d.length == 3);
        assert(noArgs1d[2] == 111);
    }

    /// solc: semanticTests/array/push/push_no_args_1d.sol
    /// @custom:key box
    function pushNoArgs1d() public {
        require(noArgs1d.length == 0);
        noArgs1d.push() = 42;
        uint y = noArgs1d.push();
        assert(y == 0);
        assert(noArgs1d.length == 2);
        assert(noArgs1d[1] == 0);
    }

    /// solc: semanticTests/array/push/push_no_args_struct.sol
    /// @custom:key box
    function pushNoArgsStructLvalue(uint y) public {
        require(y == 4096);
        require(noArgsStruct.length == 0);
        noArgsStruct.push().x = y;
        assert(noArgsStruct.length == 1);
        uint r = noArgsStruct[0].x;
        assert(r == 4096);
    }

    /// solc: semanticTests/array/delete/delete_storage_array.sol
    function deleteStorageArray() public {
        deleted.push(234);
        deleted.push(123);
        delete deleted;
        uint r = deleted.length;
        assert(r == 0);
    }

    /// solc: semanticTests/array/copying/array_copy_clear_storage.sol
    function copyShrinksStorage() public {
        cleared.push(42);
        cleared.push(42);
        cleared.push(42);
        cleared.push(42);
        uint[] memory y = new uint[](1);
        y[0] = 23;
        cleared = y;
        uint l = cleared.length;
        uint r = cleared[0];
        assert(l == 1);
        assert(r == 23);
    }

    /// solc: semanticTests/array/copying/array_copy_memory_to_storage.sol
    function copyMemoryToStorage() public {
        uint[] memory m = new uint[](3);
        m[0] = 1;
        m[1] = 2;
        m[2] = 3;
        fromMemory = m;
        assert(fromMemory[0] == m[0]);
        assert(fromMemory[1] == m[1]);
        assert(fromMemory[2] == m[2]);
        uint l = fromMemory.length;
        assert(l == 3);
    }

    /// solc: semanticTests/array/copying/array_copy_memory_to_storage.sol
    function copyMemoryFixedToStorage() public {
        uint[3] memory m;
        m[0] = 1;
        m[1] = 2;
        m[2] = 3;
        dynA = m;
        fixedB = m;
        uint a0 = dynA[0];
        uint b1 = fixedB[1];
        uint a2 = dynA[2];
        assert(a0 == 1);
        assert(b1 == 2);
        assert(a2 == 3);
        uint la = dynA.length;
        uint lb = fixedB.length;
        assert(la == lb);
    }

    /// solc: semanticTests/array/copying/nested_array_memory_to_storage.sol
    function copyNestedMemoryToStorage() public {
        uint[][] memory m = new uint[][](2);
        m[0] = new uint[](3);
        m[0][0] = 7;
        m[0][1] = 8;
        m[0][2] = 9;
        m[1] = new uint[](4);
        m[1][1] = 7;
        m[1][2] = 8;
        m[1][3] = 9;
        nestedFromMem = m;
        uint a = nestedFromMem[0][0];
        uint b = nestedFromMem[0][1];
        uint c = nestedFromMem[1][3];
        uint r = a + b + c;
        assert(r == 24);
    }

    /// solc: semanticTests/array/copying/array_copy_storage_storage_dyn_dyn.sol
    function copyStorageStorageDynDyn() public {
        dyn1 = new uint[](10);
        dyn1[5] = 4;
        dyn2 = dyn1;
        uint len = dyn2.length;
        uint val = dyn2[5];
        assert(len == 10);
        assert(val == 4);
    }

    /// solc: semanticTests/array/copying/array_copy_storage_to_memory_nested.sol
    /// @custom:key box
    function copyNestedStorageToMemory() public {
        require(nestedToMemory.length == 0);
        nestedToMemory.push();
        nestedToMemory.push();
        nestedToMemory[0].push(0);
        nestedToMemory[0].push(1);
        nestedToMemory[1].push(2);
        nestedToMemory[1].push(3);
        uint[][] memory m = nestedToMemory;
        uint l = m.length;
        uint a = m[0][1];
        uint b = m[1][0];
        uint c = m[1][1];
        assert(l == 2);
        assert(a == 1);
        assert(b == 2);
        assert(c == 3);
    }

    /// solc: semanticTests/array/copying/storage_memory_nested.sol
    /// @custom:key box
    function storageMemoryNestedFixed() public {
        require(nestedFixed.length == 0);
        for (uint i = 0; i < 4; i++)
            nestedFixed.push();
        nestedFixed[0][0] = 1;
        nestedFixed[0][3] = 2;
        nestedFixed[1][1] = 3;
        nestedFixed[1][4] = 4;
        nestedFixed[2][0] = 5;
        nestedFixed[3][2] = 6;
        nestedFixed[3][3] = 7;
        uint[5][] memory m = nestedFixed;
        uint a = m[0][0];
        uint b = m[0][3];
        uint c = m[1][1];
        uint d = m[1][4];
        uint e = m[2][0];
        uint f = m[3][2];
        uint g = m[3][3];
        assert(a == 1);
        assert(b == 2);
        assert(c == 3);
        assert(d == 4);
        assert(e == 5);
        assert(f == 6);
        assert(g == 7);
    }

    /// solc: semanticTests/array/copying/array_to_mapping.sol
    function arrayToMappingFromStorage() public {
        uint[][] memory t = new uint[][](2);
        t[0] = new uint[](2);
        t[0][0] = 10;
        t[0][1] = 11;
        t[1] = new uint[](3);
        t[1][2] = 14;
        arrMapSrc = t;
        arrMap[0] = arrMapSrc;
        uint l = arrMap[0].length;
        uint a = arrMap[0][0][1];
        uint b = arrMap[0][1][2];
        assert(l == 2);
        assert(a == 11);
        assert(b == 14);
    }

    /// solc: semanticTests/array/copying/nested_array_element_storage_to_storage.sol
    /// @custom:key box
    function nestedElementStorageToStorage() public {
        require(src1.length == 0);
        uint[][] memory t = new uint[][](2);
        t[0] = new uint[](2);
        t[0][0] = 3;
        t[0][1] = 4;
        t[1] = new uint[](2);
        t[1][0] = 5;
        t[1][1] = 6;
        src1.push();
        src1.push();
        src1[1] = t;
        dst1 = src1[1];
        uint l = dst1.length;
        assert(l == 2);
        uint d00 = dst1[0][0];
        uint s00 = src1[1][0][0];
        assert(d00 == s00);
        uint d11 = dst1[1][1];
        uint s11 = src1[1][1][1];
        assert(d11 == s11);
    }

    /// solc: semanticTests/array/copying/nested_array_element_memory_to_memory.sol
    function nestedMemoryElementToMemory() public pure {
        uint[][] memory a = new uint[][](2);
        a[0] = new uint[](1);
        a[0][0] = 7;
        a[1] = new uint[](2);
        a[1][0] = 8;
        a[1][1] = 9;
        uint[][][] memory tmp = new uint[][][](2);
        tmp[1] = a;
        uint[][] memory r = tmp[1];
        uint l = r.length;
        uint v = r[1][1];
        assert(l == 2);
        assert(v == 9);
    }

    /// solc: semanticTests/array/fixed_arrays_in_storage.sol
    function fixedArraysInStorage() public {
        ids[2] = 11;
        uint g2 = ids[2];
        assert(g2 == 11);
        ids[7] = 8;
        uint g7 = ids[7];
        assert(g7 == 8);
        fixedData[7].x = 8;
        fixedData[7].y = 9;
        fixedData[8].x = 10;
        fixedData[8].y = 11;
        uint x7 = fixedData[7].x;
        uint y7 = fixedData[7].y;
        uint x8 = fixedData[8].x;
        uint y8 = fixedData[8].y;
        assert(x7 == 8);
        assert(y7 == 9);
        assert(x8 == 10);
        assert(y8 == 11);
        uint l1 = fixedData.length;
        uint l2 = ids.length;
        assert(l1 == 1024);
        assert(l2 == 1027);
    }

    /// solc: semanticTests/array/array_storage_push_empty_length_address.sol
    /// @custom:key box
    function setGetLength(uint len) public {
        require(len == 3);
        /// @custom:key invariant len == 3
        while (addrLike.length < len)
            addrLike.push();
        /// @custom:key invariant len == 3 && addrLike.length >= len
        while (addrLike.length > len)
            addrLike.pop();
        uint r = addrLike.length;
        assert(r == len);
    }

    /// solc: semanticTests/storage/array_accessor.sol
    /// @custom:key box
    function arrayAccessor() public {
        require(dynamicData.length == 0);
        require(multipleMap[2][1][2].finalArray.length == 0);
        dynamicData.push();
        dynamicData.push();
        dynamicData.push(8);
        uint[] memory t = new uint[](128);
        smallTypeData = t;
        smallTypeData[1] = 22;
        smallTypeData[127] = 2;
        multipleMap[2][1][2].a = 3;
        for (uint i = 0; i < 4; i++)
            multipleMap[2][1][2].finalArray.push();
        multipleMap[2][1][2].finalArray[3] = 5;
        uint d2 = dynamicData[2];
        uint s1v = smallTypeData[1];
        uint s127 = smallTypeData[127];
        uint m = multipleMap[2][1][2].a;
        uint f3 = multipleMap[2][1][2].finalArray[3];
        assert(d2 == 8);
        assert(s1v == 22);
        assert(s127 == 2);
        assert(m == 3);
        assert(f3 == 5);
    }

    /// solc: semanticTests/storage/mappings_array2d_pop_delete.sol
    /// @custom:key box
    function mappingArray2dDelete(uint key, uint value) public {
        require(key == 42 && value == 64);
        require(map2d.length == 0);
        map2d.push();
        mapping(uint => uint)[] storage b = map2d[map2d.length - 1];
        b.push();
        b[b.length - 1][key] = value;
        uint r = b[b.length - 1][key];
        assert(r == 64);
        delete map2d;
        uint l = map2d.length;
        assert(l == 0);
    }

    /// solc: semanticTests/storage/mappings_array2d_pop_delete.sol
    /// @custom:key box
    function mappingArray2dPopRepush(uint key, uint value) public {
        require(key == 42 && value == 64);
        require(map2dPop.length == 0);
        map2dPop.push();
        mapping(uint => uint)[] storage b = map2dPop[map2dPop.length - 1];
        require(b.length == 0);
        b.push();
        b[b.length - 1][key] = value;
        map2dPop.pop();
        map2dPop.push();
        mapping(uint => uint)[] storage c = map2dPop[map2dPop.length - 1];
        c.push();
        uint r = c[c.length - 1][key];
        assert(r == 64);
    }

    /// solc: smtCheckerTests/array_members/push_arg_1.sol
    /// @custom:key box
    function pushArgReadsBackAtEnd(uint x) public {
        require(x == 5);
        pushArg.push(x);
        uint r = pushArg[pushArg.length - 1];
        assert(r == x);
    }

    /// solc: smtCheckerTests/array_members/push_zero_safe.sol
    function pushZeroReadsZero() public {
        zero1d.push();
        uint r = zero1d[zero1d.length - 1];
        assert(r == 0);
    }

    /// solc: smtCheckerTests/array_members/push_zero_2d_safe.sol
    function pushZero2d() public {
        zero2d.push();
        zero2d[zero2d.length - 1].push();
        uint r = zero2d[zero2d.length - 1][0];
        assert(r == 0);
    }

    /// solc: smtCheckerTests/array_members/push_push_no_args_1.sol
    function pushPushNoArgs2d() public {
        pushPush2.push().push();
        assert(pushPush2.length > 0);
        assert(pushPush2[pushPush2.length - 1].length > 0);
    }

    /// solc: smtCheckerTests/array_members/push_push_no_args_2.sol
    function pushPushNoArgs3d() public {
        pushPush3.push().push().push();
        assert(pushPush3.length > 0);
        uint last = pushPush3[pushPush3.length - 1].length;
        assert(last > 0);
        assert(pushPush3[pushPush3.length - 1][last - 1].length > 0);
    }

    /// solc: smtCheckerTests/array_members/push_as_lhs_1d.sol
    /// @custom:key box
    function pushLhs1dEmpty() public {
        require(lhs1d.length == 0);
        lhs1d.push() = 1;
        assert(lhs1d[0] == 1);
    }

    /// solc: smtCheckerTests/array_members/push_as_lhs_1d.sol
    function pushLhs1dLast() public {
        lhs1dLast.push() = 1;
        assert(lhs1dLast[lhs1dLast.length - 1] == 1);
    }

    /// solc: smtCheckerTests/array_members/push_struct_member_2.sol
    function pushStructMember2() public {
        sb2.b.push();
        tsb2.s.push();
        tsb2.s[0].b.push();
    }

    /// solc: smtCheckerTests/array_members/push_storage_ref_safe_aliasing.sol
    function pushRefAliasing() public {
        refAlias.push();
        uint[] storage b = refAlias[0];
        b.push(8);
        assert(b[b.length - 1] == 8);
        assert(refAlias[0][refAlias[0].length - 1] == 8);
    }

    /// solc: smtCheckerTests/array_members/push_storage_ref_unsafe_aliasing.sol
    function pushRefAliasingWrite() public {
        refAlias2.push();
        refAlias2[0].push();
        refAlias2[0][0] = 16;
        uint[] storage b = refAlias2[0];
        b[0] = 32;
        uint r = refAlias2[0][0];
        assert(r == 32);
    }

    /// solc: smtCheckerTests/array_members/push_as_lhs_and_rhs_1d.sol
    function pushLhsAndRhs1d() public {
        lhsRhs1d.push() = lhsRhs1d.push();
        uint length = lhsRhs1d.length;
        assert(length >= 2);
        assert(lhsRhs1d[length - 1] == 0);
        assert(lhsRhs1d[length - 1] == lhsRhs1d[length - 2]);
    }

    /// solc: smtCheckerTests/array_members/storage_pointer_push_1_safe.sol
    function storagePointerPushSafe() public {
        threeRows();
        pointer2d[2].push();
        assert(pointer2d[2].length > 0);
    }

    /// solc: smtCheckerTests/array_members/pop_2d_safe.sol
    function pop2dSafe() public {
        pop2d.push();
        pop2d[0].push();
        pop2d[0].pop();
    }

    /// solc: smtCheckerTests/array_members/pop_loop_safe.sol
    function popLoopSafe() public {
        uint l = 3;
        for (uint i = 0; i < l; ++i) {
            popLoop.push();
            popLoop.pop();
        }
    }

    /// solc: smtCheckerTests/array_members/push_overflow_1_safe_no_overflow_assumption.sol
    /// @custom:key box
    function pushKeepsFirst() public {
        require(overflow.length == 0);
        overflow.push(42);
        overflow.push(23);
        assert(overflow[0] == 42);
    }

    /// solc: smtCheckerTests/array_members/push_overflow_2_safe_no_overflow_assumption.sol
    /// @custom:key box
    function pushLoopKeepsFirst(uint l) public {
        require(l == 3);
        require(overflow2.length == 0);
        overflow2.push(42);
        overflow2.push(84);
        for (uint i = 0; i < l; ++i)
            overflow2.push(23);
        assert(overflow2[0] == 42);
    }

    /// solc: smtCheckerTests/array_members/length_basic.sol
    function lengthBasic() public view {
        uint x = lenA.length;
        uint y = x;
        assert(lenA.length == y);
    }

    /// solc: smtCheckerTests/array_members/length_assignment_storage_to_storage.sol
    function lengthStorageToStorage() public {
        lenB = lenA;
        uint l2 = lenB.length;
        uint l1 = lenA.length;
        assert(l2 == l1);
    }

    /// solc: smtCheckerTests/array_members/length_copy_storage_to_memory.sol
    function lengthStorageToMemory() public view {
        uint[] memory marr = lenC;
        assert(marr.length == lenC.length);
    }

    /// solc: smtCheckerTests/array_members/length_copy_memory_to_storage.sol
    function lengthMemoryToStorage() public {
        uint[] memory marr = new uint[](3);
        lenD = marr;
        uint l = lenD.length;
        assert(marr.length == l);
    }

    /// solc: smtCheckerTests/array_members/length_1d_assignment_2d_memory_to_memory.sol
    function length2dMemoryToMemory() public pure {
        uint[][] memory arr = new uint[][](2);
        arr[0] = new uint[](5);
        uint[][] memory arr2 = arr;
        assert(arr2[0].length == arr[0].length);
        assert(arr.length == arr2.length);
    }

    /// solc: smtCheckerTests/array_members/length_1d_copy_2d_storage_to_memory.sol
    /// @custom:key box
    function length2dStorageToMemory() public {
        require(same2.length == 0);
        same2.push();
        same2.push();
        same2.push();
        same2.push();
        uint[][] memory arr2 = same2;
        uint a = arr2[0].length;
        uint b = same2[0].length;
        assert(a == b);
        uint c = arr2.length;
        uint d = same2.length;
        assert(c == d);
    }

    /// solc: smtCheckerTests/array_members/length_1d_mapping_array_2.sol
    /// @custom:key box
    function lengthMappingArray(uint x, uint y) public view {
        require(x == 3 && y == 3);
        uint a = lenMap[x].length;
        uint b = lenMap[y].length;
        assert(a == b);
    }

    /// solc: smtCheckerTests/array_members/length_1d_mapping_array_2d_1.sol
    /// @custom:key box
    function lengthMappingArray2d(uint x, uint y) public {
        require(x == 3 && y == 3);
        lenMap2d[x].push();
        uint a = lenMap2d[x][0].length;
        uint b = lenMap2d[y][0].length;
        assert(a == b);
    }

    /// solc: smtCheckerTests/array_members/length_1d_struct_array_2d_1.sol
    /// @custom:key box
    function lengthStructArray2d() public {
        require(s1.arr.length == 0);
        require(s2.arr.length == 0);
        s1.arr.push();
        s2.arr.push();
        require(s1.arr[0].length == 0);
        require(s2.arr[0].length == 0);
        s1.arr[0].push();
        s1.arr[0].push();
        s1.arr[0].push();
        s2.arr[0].push();
        s2.arr[0].push();
        s2.arr[0].push();
        uint a = s1.arr[0].length;
        uint b = s2.arr[0].length;
        assert(a == b);
    }

    /// solc: smtCheckerTests/array_members/length_function_call.sol
    /// @custom:key box
    function lengthFunctionCall() public view {
        require(fnArr.length == 0);
        uint[] memory r = emptyMemory();
        uint l = fnArr.length;
        assert(l == r.length);
    }

    /// solc: smtCheckerTests/array_members/length_same_after_assignment.sol
    /// @custom:key box
    function lengthSameAfterMemoryCopy() public {
        require(sameMem.length == 0);
        sameMem.push();
        sameMem.push();
        sameMem.push();
        sameMem.push();
        uint[] memory arr2 = sameMem;
        arr2[2] = 3;
        assert(sameMem.length == arr2.length);
    }

    /// solc: smtCheckerTests/array_members/length_same_after_assignment_2.sol
    /// @custom:key box
    function lengthSameAfterElementWrite() public {
        require(same4.length == 0);
        same4.push();
        same4.push();
        same4.push();
        same4.push();
        require(same4[2].length == 0);
        same4[2].push();
        same4[2].push();
        same4[2].push();
        same4[2].push();
        uint x = same4[2].length;
        uint y = same4[3].length;
        uint z = same4.length;
        same4[2][3] = 444;
        assert(same4[2].length == x);
        assert(same4[3].length == y);
        assert(same4.length == z);
    }

    /// solc: smtCheckerTests/array_members/length_same_after_assignment_3.sol
    /// @custom:key box
    function lengthSameAfterRowCopy() public {
        require(same3.length == 0);
        for (uint i = 0; i < 9; i++)
            same3.push();
        require(same3[5].length == 0);
        require(same3[8].length == 0);
        uint x = same3[2].length;
        uint y = same3[3].length;
        uint z = same3.length;
        uint t = same3[5].length;
        same3[5] = same3[8];
        assert(same3[2].length == x);
        assert(same3[3].length == y);
        assert(same3.length == z);
        assert(same3[5].length == t);
    }

    /// solc: semanticTests/array/push/array_push_nested.sol
    /// @custom:key box
    function pushNested() public {
        require(nestedP.length == 0);
        nestedP.push();
        assert(nestedP.length == 1);
        assert(nestedP[0].length == 0);
        nestedP[0].push();
        assert(nestedP[0].length == 1);
        assert(nestedP[0][0] == 0);
    }

    function setX(S storage s, uint y) internal {
        s.x = y;
    }

    /// solc: semanticTests/array/push/push_no_args_struct.sol
    /// @custom:key box
    function pushNoArgsStruct(uint y) public {
        require(y == 42);
        require(noArgsStruct.length == 0);
        S storage s = noArgsStruct.push();
        setX(s, y);
        setX(noArgsStruct.push(), 84);
        assert(noArgsStruct.length == 2);
        uint a0 = noArgsStruct[0].x;
        uint a1 = noArgsStruct[1].x;
        assert(a0 == 42);
        assert(a1 == 84);
    }

    /// solc: semanticTests/array/copying/array_copy_storage_storage_static_dynamic.sol
    function copyStaticToDynamic() public {
        staticData1[8] = 4;
        staticData2 = staticData1;
        uint x = staticData2.length;
        uint y = staticData2[8];
        assert(x == 9);
        assert(y == 4);
    }

    /// solc: semanticTests/array/copying/array_copy_storage_storage_static_static.sol
    function copyStaticToLargerStatic() public {
        big[30] = 4;
        big[2] = 7;
        big[3] = 9;
        small[3] = 8;
        big = small;
        uint x = big[3];
        uint y = big[30];
        assert(x == 8);
        assert(y == 0);
    }

    /// solc: smtCheckerTests/array_members/push_as_lhs_2d.sol
    function pushLhs2dLast() public {
        lhs2d.push().push() = 2;
        assert(lhs2d.length > 0);
        assert(lhs2d[lhs2d.length - 1].length == 1);
        assert(lhs2d[lhs2d.length - 1][lhs2d[lhs2d.length - 1].length - 1] == 2);
    }

    /// solc: smtCheckerTests/array_members/push_as_lhs_3d.sol
    function pushLhs3dLast() public {
        lhs3d.push().push().push() = 2;
        uint length1 = lhs3d.length;
        uint length2 = lhs3d[length1 - 1].length;
        uint length3 = lhs3d[length1 - 1][length2 - 1].length;
        assert(length1 > 0);
        assert(length2 == 1);
        assert(length3 == 1);
        assert(lhs3d[length1 - 1][length2 - 1][length3 - 1] == 2);
    }

    /// solc: smtCheckerTests/array_members/length_1d_assignment_2d_storage_to_storage.sol
    /// @custom:key box
    function length2dStorageToStorage() public {
        require(lenArr.length == 0);
        require(lenArr2.length == 0);
        lenArr.push();
        lenArr.push();
        lenArr2.push();
        lenArr2.push();
        uint a = lenArr2[0].length;
        uint b = lenArr[0].length;
        assert(a == b);
        uint c = lenArr2.length;
        uint d = lenArr.length;
        assert(c == d);
    }

    /// solc: semanticTests/array/push/array_push_nested_from_memory.sol
    function pushNestedFromMemory() public {
        delete nestedFromMemory;
        uint[] memory m = new uint[](3);
        m[0] = 1;
        nestedFromMemory.push(m);
        assert(nestedFromMemory.length == 1);
        assert(nestedFromMemory[0].length == m.length);
        assert(nestedFromMemory[0].length > 0);
        uint r = nestedFromMemory[0][0];
        assert(r == 1);
    }

    /// solc: smtCheckerTests/array_members/push_as_lhs_compound_assignment.sol
    /// @custom:key box
    function pushLhsCompound() public {
        require(compound.length == 0);
        compound.push() -= 1;
        assert(compound[0] < 0);
    }

    /// solc: smtCheckerTests/array_members/push_as_lhs_struct.sol
    function pushLhsStruct() public {
        sb.b.push() = tsb.s.b.push();
        int l = sb.b[sb.b.length - 1];
        int r = tsb.s.b[tsb.s.b.length - 1];
        assert(l == r);
    }

    /// solc: smtCheckerTests/array_members/push_2d_arg_1_safe.sol
    function pushMemoryRowThenValue() public {
        uint[] memory x = new uint[](2);
        uint y = 9;
        push2dArg.push(x);
        push2dArg[0].push(y);
        assert(push2dArg[0][push2dArg[0].length - 1] == y);
    }

    /// solc: smtCheckerTests/array_members/storage_pointer_push_1.sol
    function storagePointerPush() public {
        threeRows().push();
        assert(pointer2d[2].length > 0);
    }

    /// solc: semanticTests/array/push/array_push_struct.sol
    /// @custom:key box
    function pushStructFromMemory() public {
        require(structData.length == 0);
        PS memory s;
        s.a = 2;
        s.b = 3;
        s.c[2] = 4;
        s.d = new uint[](4);
        s.d[2] = 5;
        structData.push(s);
        uint a = structData[0].a;
        uint b = structData[0].b;
        uint c = structData[0].c[2];
        uint d = structData[0].d[2];
        assert(a == 2);
        assert(b == 3);
        assert(c == 4);
        assert(d == 5);
    }

}
