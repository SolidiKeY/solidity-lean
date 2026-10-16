// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

uint constant FILE_LEVEL_LIMIT = 42;

enum FileLevelColor { Red, Green, Blue }

struct FileLevelPair { uint left; uint right; }

type Wei is uint;

function fileLevelTwice(uint v) pure returns (uint) {
    return 2 * v;
}

library PairLib {
    uint constant UNIT = 10;

    function bump(uint v) internal pure returns (uint) {
        return v + UNIT;
    }

    function swap(FileLevelPair storage p) internal {
        uint l = p.left;
        p.left = p.right;
        p.right = l;
    }
}

/// The taclet example suite. There are no `.key` problem files: the loader synthesizes one
/// obligation per function of this contract, calling it with postcondition `true`, so every test
/// is real Solidity that `solc` parses and type-checks.
///
/// Conventions:
///   - every function is `public` and returns nothing;
///   - a function may take arguments: the loader binds each one to an unconstrained program
///     variable, so the function must be tagged `/// @custom:key box` and state the values its
///     asserts rely on in one conjoined `require(x == 5 && y == 7)` — the box turns it into an
///     assumption, playing the role of the old `.key` precondition `x = 5 & y = 7`. Bounds on
///     storage stay in their own ordered requires (next point), since each one guards the
///     evaluation of the next;
///   - what the test observes is stated in the body with `assert` — a value the old `.key`
///     postcondition named is bound to a local first, since a test function returns nothing
///     (internal helpers may `return` values);
///   - what the test assumes is stated with `require`, and the function is then tagged
///     `/// @custom:key box`. `require` is an assumption under a box modality and an obligation
///     under a diamond (docs/require-assert.md), so the tag is what makes it an assumption.
///     Tag only functions that need it: a box discharges a reverting execution vacuously, so an
///     untagged function additionally proves that it never reverts.
///   - a tagged function must `require` every bound its body relies on, outermost first
///     (`require(2 < matrix.length);` before `require(3 < matrix[2].length);`).
contract TestSuite {
    using PairLib for uint;

    struct Token { uint value; }
    struct Account { uint balance; Token token; }
    struct Person { Account account; uint age; }
    struct Basket { uint[] items; }
    struct Ledger { uint nonce; mapping(uint => uint) balances; }
    struct LedgerUse { Ledger ledger; }
    struct TokenBucket { Token[] tokens; }
    struct Toggle { bool on; uint n; }
    struct Triple { uint[3] items; uint tag; }
    struct Tree { uint v; mapping(uint => Tree) kids; }

    uint total;
    uint age;
    address owner;
    uint balance;
    int signedTotal;
    bool flag;
    bool flag2;

    uint[] values;
    int[] signedValues;
    uint[] a;
    uint[][] matrix;
    uint[3] fixedValues;
    uint[3][] rows;
    uint[9] copySource9;
    uint[] copyTargetDyn;
    uint[3][2] fixedGrid;
    mapping(uint => uint[3])[2] fixedMapsOfFixed;
    mapping(uint => uint[3])[] dynMapsOfFixed;
    uint[40] copyBig;
    uint[20] copySmall;
    uint localOut;
    mapping(uint => uint[3]) fixedByKey;
    Token[2] fixedTokens;
    mapping(uint => uint)[2] fixedMaps;
    Triple triple;
    Triple triple2;
    bool[] boolFlags;

    mapping(uint => uint) balances;
    mapping(uint => Person) people;
    mapping(uint => bool) flags;
    mapping(uint => uint) valuesMap;
    mapping(uint => Account) accountMap;

    Person[] persons;
    Person alice;
    Person bob;
    Toggle toggle;

    Ledger ledger;
    Token tok;
    Token[] tokens;
    TokenBucket bucket;
    TokenBucket[] buckets;
    Basket basketA;
    Basket basketB;
    LedgerUse[] ledgerUses;

    mapping(uint => mapping(uint => uint)) grid;
    mapping(uint => Ledger) ledgerMap;
    mapping(uint => uint)[] mapArray;
    mapping(bool => uint) boolKeyed;
    Tree tree;
    FileLevelPair pair;

    uint constant LIMIT = 7;
    enum Phase { Open, Closed }

    // ── Arithmetic ──

    /// @custom:key box
    function additionStorageWrite(uint x, uint y) public {
        require(x == 5 && y == 7);
        alice.age = x + y;
        uint r = alice.age;
        assert(r == 12);
    }

    // ── Storage: root ──

    function storageRootReadWrite() public {
        age = 34;
        uint r = age;
        assert(r == 34);
    }

    // ── Storage: field ──

    function storageFieldWriteRead() public {
        alice.age = 34;
        uint r = alice.age;
        assert(r == 34);
    }

    function storageFieldDeepAddAssign() public {
        alice.account.balance = 30;
        alice.account.balance += 4;
        uint r = alice.account.balance;
        assert(r == 34);
    }

    function storageFieldGlobalAge() public {
        alice.age = 34;
        assert(alice.age == 34);
        uint r = alice.age;
        assert(r == 34);
    }

    // ── Storage: alias ──

    function storageAliasWrite() public {
        Person storage p = alice;
        Account storage acc = p.account;
        acc.balance = 100;
        p.account.token.value = 3;
        assert(alice.account.balance == 100);
        assert(alice.account.token.value == 3);
    }

    // ── Storage: index ──

    function storageIndexRootMapping() public {
        balances[1] = 42;
        uint r = balances[1];
        assert(r == 42);
    }

    /// @custom:key box
    function storageIndexAddAssign() public {
        require(1 < values.length);
        values[1] = 40;
        values[1] += 2;
        uint r = values[1];
        assert(r == 42);
    }

    function storageIndexMappingAddAssign() public {
        balances[1] = 40;
        balances[1] += 2;
        uint r = balances[1];
        assert(r == 42);
    }

    /// @custom:key box
    function storageIndexArrayAddAssignOutOfBoundsReverts() public {
        require(values.length == 0);
        values[1] += 2;
        assert(false);
    }

    /// @custom:key box
    function storageIndexArrayReadOutOfBoundsReverts() public view {
        require(values.length == 0);
        uint r = values[1];
        assert(r != r);
    }

    /// @custom:key box
    function storageIndexReadComplexReceiverBindLocalRoot() public {
        require(0 < bucket.tokens.length);
        bucket.tokens[0].value = 9;
        Token storage t = bucket.tokens[0];
        uint r = t.value;
        assert(r == 9);
    }

    /// @custom:key box
    function storageIndexWriteComplexReceiverCopySource() public {
        require(0 < bucket.tokens.length);
        alice.account.token.value = 7;
        Token storage tokRef = alice.account.token;
        bucket.tokens[0] = tokRef;
        uint r = bucket.tokens[0].value;
        assert(r == 7);
    }

    function storageFieldWriteRootRhsComplexReceiver() public {
        tok.value = 7;
        alice.account.token = tok;
        uint r = alice.account.token.value;
        assert(r == 7);
    }

    function storageIndexWriteRootRhsComplexReceiver() public {
        total = 9;
        ledger.balances[3] = total;
        uint r = ledger.balances[3];
        assert(r == 9);
    }

    // ── Storage: push ──

    /// @custom:key box
    function storagePushValue() public {
        require(values.length == 2);
        values.push(42);
        assert(values[2] == 42);
        assert(values.length == 3);
    }

    /// @custom:key box
    function storagePushComplexReceiverNonsimpleArg(uint x, uint y) public {
        require(0 < matrix.length);
        require(matrix[0].length == 0);
        require(x == 40 && y == 2);
        matrix[0].push(x + y);
        uint r = matrix[0][0];
        assert(r == 42);
    }

    /// @custom:key box
    function storagePushValueCopySource() public {
        require(tokens.length == 0);
        tok.value = 7;
        tokens.push(tok);
        assert(tokens[0].value == 7);
    }

    /// @custom:key box
    function storagePushMemoryCopySource() public {
        require(matrix.length == 0);
        uint[] memory row = new uint[](2);
        row[1] = 7;
        matrix.push(row);
        uint r = matrix[0][1];
        assert(r == 7);
        assert(matrix[0].length == 2);
    }

    /// @custom:key box
    function storagePushMemoryStructCopySource() public {
        require(tokens.length == 0);
        Token memory t;
        t.value = 7;
        tokens.push(t);
        t.value = 8;
        assert(tokens[0].value == 7);
    }

    function storagePushReturnPrimitiveBindComplexReceiver() public {
        delete matrix;
        matrix.push();
        matrix[0].push(4);
        uint y = matrix[0].push();
        assert(y == 0);
        assert(matrix[0].length == 2);
    }

    function storagePushCompoundTarget() public {
        delete values;
        values.push() += 5;
        values.push() *= 3;
        assert(values[0] == 5 && values[1] == 0);
        assert(values.length == 2);
    }

    function storagePushDivModTarget() public {
        delete values;
        values.push() /= 2;
        values.push() %= 2;
        assert(values[0] == 0 && values[1] == 0);
        assert(values.length == 2);
    }

    function storagePushIncrementTarget() public {
        delete values;
        ++values.push();
        values.push()++;
        assert(values[0] == 1 && values[1] == 1);
        assert(values.length == 2);
    }

    function storagePushCompoundSigned() public {
        delete signedValues;
        signedValues.push() -= 4;
        --signedValues.push();
        signedValues.push()--;
        assert(signedValues[0] == -4 && signedValues[1] == -1 && signedValues[2] == -1);
        assert(signedValues.length == 3);
    }

    function valuesRef() internal view returns (uint[] storage) {
        return values;
    }

    function storagePushPopCallReceiver() public {
        delete values;
        valuesRef().push();
        valuesRef().push(42);
        valuesRef().pop();
        assert(values.length == 1);
        assert(values[0] == 0);
    }

    function newArrayCaptureStorageRoot() public {
        values = new uint[](3);
        assert(values.length == 3);
        assert(values[2] == 0);
    }

    // ── Require / assert: literal operand ──

    function requireTrueLiteral() public pure {
        require(true);
        assert(true);
    }

    /// @custom:key box
    function requireFalseLiteral() public pure {
        require(false);
        assert(false);
    }

    // ── Storage: bool ──

    function storageBoolRootReadWrite() public {
        flag = true;
        bool r = flag;
        assert(r);
    }

    function storageBoolRootCopy() public {
        flag = true;
        flag2 = flag;
        bool r = flag2;
        assert(r);
    }

    function storageBoolFieldRead() public {
        toggle.on = true;
        bool r = toggle.on;
        assert(r);
    }

    function storageBoolMappingRead() public {
        flags[2] = true;
        bool r = flags[2];
        assert(r);
    }

    /// @custom:key box
    function storageBoolArrayRead() public {
        require(boolFlags.length == 1);
        boolFlags[0] = true;
        bool r = boolFlags[0];
        assert(r);
    }

    function storageBoolFieldStoreRoot() public {
        toggle.on = true;
        flag = toggle.on;
        bool r = flag;
        assert(r);
    }

    // ── Memory ──

    function memoryDeclDefault() public pure {
        Person memory carol;
        uint r = carol.age;
        assert(r == 0);
    }

    function memoryArrayIndex() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 33;
        uint r = xs[1];
        assert(r == 33);
    }

    function memoryNewIntoStructField() public pure {
        Basket memory basket;
        basket.items = new uint[](2);
        assert(basket.items.length == 2);
    }

    function memoryNewIntoNestedField() public pure {
        Basket[] memory bs = new Basket[](1);
        bs[0].items = new uint[](3);
        assert(bs[0].items.length == 3);
    }

    function memoryNewIntoIndex() public pure {
        uint[][] memory xs = new uint[][](1);
        xs[0] = new uint[](3);
        assert(xs[0].length == 3);
    }

    function storageNewIntoField() public {
        basketA.items = new uint[](2);
        assert(basketA.items.length == 2);
    }

    // ── mainFeatures ──

    /// @custom:key box
    function testStorageComplexReceiverEmptyPush() public {
        require(bucket.tokens.length == 0);
        bucket.tokens.push();
        Token[] storage bt = bucket.tokens;
        assert(bt.length == 1);
    }

    // ── generated: one function per example ──

    function additionBothStorage() public {
        alice.age = 10;
        bob.age = 5;
        uint r = alice.age + bob.age;
        assert(r == 15);
    }

    function additionSimple() public pure {
        uint r = 1 + 2;
        assert(r == 3);
    }

    function additionStorageRead() public {
        alice.age = 10;
        uint r = alice.age + 1;
        assert(r == 11);
    }

    function divisionSimple() public pure {
        uint r = 8 / 2;
        assert(r == 4);
    }

    function greaterEqualSimple() public pure {
        bool r = 5 >= 6;
        assert(!r);
    }

    function greaterThanSimple() public pure {
        bool r = 5 > 3;
        assert(r);
    }

    function lessEqualSimple() public pure {
        bool r = 5 <= 5;
        assert(r);
    }

    function lessThanSimple() public pure {
        bool r = 3 < 5;
        assert(r);
    }

    function logicalAndSimple() public pure {
        bool r = true && false;
        assert(!r);
    }

    function logicalAndShortCircuitRhs() public pure {
        uint x = 5;
        bool r = x == 5 && x + 1 == 6;
        assert(r);
    }

    function logicalNotSimple() public pure {
        bool r = !false;
        assert(r);
    }

    function logicalOrSimple() public pure {
        bool r = true || false;
        assert(r);
    }

    function logicalOrShortCircuitRhs() public pure {
        uint x = 5;
        bool r = x == 4 || x + 1 == 6;
        assert(r);
    }

    function ternaryCaptureCond() public pure {
        uint x = 5;
        uint r = x == 5 ? x + 1 : 0;
        assert(r == 6);
    }

    function ternaryToIf() public pure {
        bool b = true;
        uint r = b ? 1 : 2;
        assert(r == 1);
    }

    function ifUnfold() public pure {
        uint x = 5;
        uint r = 0;
        if (x == 4) r = 1;
        assert(r == 0);
    }

    function ifElseUnfold() public pure {
        uint x = 5;
        uint r = 0;
        if (x == 5) r = 1; else r = 2;
        assert(r == 1);
    }

    function ifSplit() public pure {
        bool b = true;
        uint r = 0;
        if (b) r = 1;
        assert(r == 1);
    }

    function ifElseSplit() public pure {
        bool b = false;
        uint r = 0;
        if (b) {
            r = 1;
        } else {
            r = 2;
        }
        assert(r == 2);
    }

    function ifTrue() public pure {
        uint r = 0;
        if (true) r = 1;
        assert(r == 1);
    }

    function ifFalse() public pure {
        uint r = 0;
        if (false) r = 1;
        assert(r == 0);
    }

    function ifElseTrue() public pure {
        uint r = 0;
        if (true) r = 1; else r = 2;
        assert(r == 1);
    }

    function ifElseFalse() public pure {
        uint r = 0;
        if (false) r = 1; else r = 2;
        assert(r == 2);
    }

    function ifElseNegated() public pure {
        bool b = false;
        uint r = 0;
        if (!b) r = 1; else r = 2;
        assert(r == 1);
    }

    function memoryDeepField() public pure {
        Person memory carol;
        carol.account.balance = 10;
        uint r = carol.account.balance;
        assert(r == 10);
    }

    function memoryFieldAddAssign() public pure {
        Person memory carol;
        carol.age = 30;
        carol.age += 4;
        uint r = carol.age;
        assert(r == 34);
    }

    function memoryFieldSubAssign() public pure {
        Person memory carol;
        carol.age = 30;
        carol.age -= 4;
        uint r = carol.age;
        assert(r == 26);
    }

    function memoryFieldMulAssign() public pure {
        Person memory carol;
        carol.age = 7;
        carol.age *= 4;
        uint r = carol.age;
        assert(r == 28);
    }

    function memoryFieldDivAssign() public pure {
        Person memory carol;
        carol.age = 30;
        carol.age /= 5;
        uint r = carol.age;
        assert(r == 6);
    }

    function memoryFieldModAssign() public pure {
        Person memory carol;
        carol.age = 30;
        carol.age %= 7;
        uint r = carol.age;
        assert(r == 2);
    }

    function memoryFieldAddAssignUnfold() public pure {
        Person memory carol;
        carol.account.balance = 20;
        carol.account.balance += 4;
        uint r = carol.account.balance;
        assert(r == 24);
    }

    function memoryFieldAddAssignNse() public pure {
        Person memory carol;
        carol.age = 30;
        carol.age += 2 * 3;
        uint r = carol.age;
        assert(r == 36);
    }

    function memoryFieldPreincrement() public pure {
        Person memory carol;
        carol.age = 30;
        ++carol.age;
        uint r = carol.age;
        assert(r == 31);
    }

    function memoryFieldPostincrement() public pure {
        Person memory carol;
        carol.age = 30;
        carol.age++;
        uint r = carol.age;
        assert(r == 31);
    }

    function memoryFieldPredecrement() public pure {
        Person memory carol;
        carol.age = 30;
        --carol.age;
        uint r = carol.age;
        assert(r == 29);
    }

    function memoryFieldPostdecrement() public pure {
        Person memory carol;
        carol.age = 30;
        carol.age--;
        uint r = carol.age;
        assert(r == 29);
    }

    function memoryFieldPreincrementAssignment() public pure {
        Person memory carol;
        carol.age = 30;
        uint r = ++carol.age;
        assert(r == 31);
        assert(carol.age == 31);
    }

    function memoryFieldPostincrementAssignment() public pure {
        Person memory carol;
        carol.age = 30;
        uint r = carol.age++;
        assert(r == 30);
        assert(carol.age == 31);
    }

    function memoryFieldPredecrementAssignment() public pure {
        Person memory carol;
        carol.age = 30;
        uint r = --carol.age;
        assert(r == 29);
        assert(carol.age == 29);
    }

    function memoryFieldPostdecrementAssignment() public pure {
        Person memory carol;
        carol.age = 30;
        uint r = carol.age--;
        assert(r == 30);
        assert(carol.age == 29);
    }

    function memoryFieldPreincrementUnfold() public pure {
        Person memory carol;
        carol.account.balance = 20;
        ++carol.account.balance;
        uint r = carol.account.balance;
        assert(r == 21);
    }

    function memoryFieldAlias() public pure {
        Person memory carol;
        Account memory acc = carol.account;
        acc.balance = 100;
        uint r = carol.account.balance;
        assert(r == 100);
    }

    function memoryFieldReferenceAssign() public pure {
        Person memory carol;
        Person memory david;
        Account memory pv = david.account;
        carol.account = pv;
        carol.account.balance = 60;
        uint r = david.account.balance;
        assert(r == 60);
    }

    function memoryIndexArrayAddAssign() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        xs[1] += 2;
        uint r = xs[1];
        assert(r == 42);
    }

    function memoryIndexArraySubAssign() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        xs[1] -= 2;
        uint r = xs[1];
        assert(r == 38);
    }

    function memoryIndexArrayMulAssign() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 7;
        xs[1] *= 6;
        uint r = xs[1];
        assert(r == 42);
    }

    function memoryIndexArrayDivAssign() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        xs[1] /= 8;
        uint r = xs[1];
        assert(r == 5);
    }

    function memoryIndexArrayModAssign() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        xs[1] %= 7;
        uint r = xs[1];
        assert(r == 5);
    }

    function memoryIndexArrayAddAssignUnfold() public pure {
        Basket memory basket;
        uint[] memory xs = new uint[](4);
        basket.items = xs;
        basket.items[1] = 40;
        basket.items[1] += 2;
        uint r = basket.items[1];
        assert(r == 42);
    }

    function memoryIndexArrayPreincrementUnfold() public pure {
        Basket memory basket;
        uint[] memory xs = new uint[](4);
        basket.items = xs;
        basket.items[1] = 40;
        ++basket.items[1];
        uint r = basket.items[1];
        assert(r == 41);
    }

    function memoryIndexArrayPreincrement() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        ++xs[1];
        uint r = xs[1];
        assert(r == 41);
    }

    function memoryIndexArrayPostdecrement() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        xs[1]--;
        uint r = xs[1];
        assert(r == 39);
    }

    function memoryIndexArrayPostincrementAssignment() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        uint r = xs[1]++;
        assert(r == 40);
        assert(xs[1] == 41);
    }

    function memoryIndexArrayPredecrementAssignment() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        uint r = --xs[1];
        assert(r == 39);
        assert(xs[1] == 39);
    }

    /// @custom:key box
    function memoryIndexWriteNse(uint i, uint lhs, uint rhs) public pure {
        require(i == 1 && lhs == 4 && rhs == 5);
        uint[] memory xs = new uint[](4);
        xs[i+1] = lhs + rhs;
        uint r = xs[i+1];
        assert(r == 9);
    }

    function memoryRootAlias() public pure {
        Person memory carol;
        Person memory david;
        david.age = 40;
        carol = david;
        carol.age = 41;
        uint r = david.age;
        assert(r == 41);
    }

    function memoryRootDeleteFresh() public pure {
        Person memory carol;
        delete carol;
    }

    function memoryStructArrayIndex() public pure {
        Basket memory basket;
        uint[] memory xs = new uint[](4);
        basket.items = xs;
        basket.items[1] = 33;
        uint r = basket.items[1];
        assert(r == 33);
    }

    function memoryToStorage() public {
        Person memory carol;
        carol.age = 44;
        alice = carol;
        uint r = alice.age;
        assert(r == 44);
    }

    function memoryToStorageIndexMappingCopyRootExample() public {
        Person memory carol;
        carol.age = 6;
        people[1] = carol;
        uint r = people[1].age;
        assert(r == 6);
    }

    /// @custom:key box
    function memoryToStorageIndexArrayCopyRootExample() public {
        require(0 < persons.length);
        Person memory carol;
        carol.age = 6;
        persons[0] = carol;
        uint r = persons[0].age;
        assert(r == 6);
    }

    /// @custom:key box
    function memoryToStorageIndexArrayCopyRootOutOfBoundsReverts() public {
        require(persons.length == 0);
        Person memory carol;
        persons[0] = carol;
        assert(false);
    }

    function moduloSimple() public pure {
        uint r = 7 % 3;
        assert(r == 1);
    }

    function multiplicationSimple() public pure {
        uint r = 3 * 4;
        assert(r == 12);
    }

    function notEqualSimple() public pure {
        bool r = 3 != 4;
        assert(r);
    }

    function powerSimple() public pure {
        uint r = 2 ** 3;
        assert(r == 8);
    }

    /// @custom:key box
    function requireGuardBox(uint x) public {
        require(x > 0);
        age = 1;
        uint r = age;
        assert(r == 1);
    }

    function requireHoldsDiamond() public {
        uint x = 5;
        require(x > 0);
        total = x;
        uint r = total;
        assert(r == 5);
    }

    function storageAliasRebindAlias() public {
        Person storage alicePath = alice;
        bob.age = 20;
        alicePath = bob;
        uint r = alicePath.age;
        assert(r == 20);
    }

    function storageDeepFieldPostincrement() public {
        alice.account.balance = 100;
        alice.account.balance++;
        uint r = alice.account.balance;
        assert(r == 101);
    }

    function storageDeepFieldPreincrement() public {
        alice.account.balance = 100;
        ++alice.account.balance;
        uint r = alice.account.balance;
        assert(r == 101);
    }

    function storageFieldAddAssign() public {
        alice.age = 30;
        alice.age += 4;
        uint r = alice.age;
        assert(r == 34);
    }

    function storageFieldCopyStruct() public {
        bob.account.balance = 11;
        Account storage acc = bob.account;
        alice.account = acc;
        uint r = alice.account.balance;
        assert(r == 11);
    }

    function storageFieldCopyValueField() public {
        bob.age = 30;
        alice.age = bob.age;
        uint r = alice.age;
        assert(r == 30);
    }

    function storageFieldDeepDivAssign() public {
        alice.account.balance = 36;
        alice.account.balance /= 4;
        uint r = alice.account.balance;
        assert(r == 9);
    }

    function storageFieldDeepModAssign() public {
        alice.account.balance = 37;
        alice.account.balance %= 4;
        uint r = alice.account.balance;
        assert(r == 1);
    }

    function storageFieldDeepMulAssign() public {
        alice.account.balance = 8;
        alice.account.balance *= 3;
        uint r = alice.account.balance;
        assert(r == 24);
    }

    function storageFieldDeepSubAssign() public {
        alice.account.balance = 30;
        alice.account.balance -= 4;
        uint r = alice.account.balance;
        assert(r == 26);
    }

    function storageFieldDeepWriteRead() public {
        alice.account.balance = 34;
        uint r = alice.account.balance;
        assert(r == 34);
    }

    function storageFieldDelete() public {
        alice.age = 30;
        delete alice.age;
        uint r = alice.age;
        assert(r == 0);
    }

    function storageFieldDeleteThenCopy() public {
        bob.account.balance = 10;
        delete bob.account;
        alice.account = bob.account;
        uint r = alice.account.balance;
        assert(r == 0);
    }

    function storageFieldDeleteThenCopyDeep() public {
        bob.account.token.value = 7;
        delete bob.account;
        alice.account = bob.account;
        uint r = alice.account.token.value;
        assert(r == 0);
    }

    function storageFieldDivAssign() public {
        alice.age = 30;
        alice.age /= 5;
        uint r = alice.age;
        assert(r == 6);
    }

    function storageFieldModAssign() public {
        alice.age = 30;
        alice.age %= 7;
        uint r = alice.age;
        assert(r == 2);
    }

    function storageFieldMulAssign() public {
        alice.age = 7;
        alice.age *= 4;
        uint r = alice.age;
        assert(r == 28);
    }

    function storageFieldPostdecrementAssign() public {
        alice.age = 30;
        uint r = alice.age--;
        assert(r == 30);
    }

    function storageFieldPostdecrement() public {
        alice.age = 30;
        alice.age--;
        uint r = alice.age;
        assert(r == 29);
    }

    function storageFieldPostincrementAssign() public {
        alice.age = 30;
        uint r = alice.age++;
        assert(r == 30);
    }

    function storageFieldPostincrement() public {
        alice.age = 30;
        alice.age++;
        uint r = alice.age;
        assert(r == 31);
    }

    function storageFieldPredecrementAssign() public {
        alice.age = 30;
        uint r = --alice.age;
        assert(r == 29);
    }

    function storageFieldPredecrement() public {
        alice.age = 30;
        --alice.age;
        uint r = alice.age;
        assert(r == 29);
    }

    function storageFieldPreincrementAssign() public {
        alice.age = 30;
        uint r = ++alice.age;
        assert(r == 31);
    }

    function storageFieldPreincrement() public {
        alice.age = 30;
        ++alice.age;
        uint r = alice.age;
        assert(r == 31);
    }

    function storageFieldReadBindLocal() public {
        Account storage acc = alice.account;
        bob.account.balance = 42;
        acc = bob.account;
        uint r = acc.balance;
        assert(r == 42);
    }

    function storageFieldReadStoreRoot() public {
        alice.age = 17;
        total = alice.age;
        uint r = total;
        assert(r == 17);
    }

    function storageFieldSubAssign() public {
        alice.age = 30;
        alice.age -= 5;
        uint r = alice.age;
        assert(r == 25);
    }

    function storageFieldWriteCaptureSrc() public {
        bob.account.balance = 11;
        alice.account = bob.account;
        uint r = alice.account.balance;
        assert(r == 11);
    }

    /// @custom:key box
    function storageFieldWriteRhsCapture(uint x, uint y, uint z) public {
        require(x == 1 && y == 2 && z == 3);
        alice.age = x + y*z;
        uint r = alice.age;
        assert(r == 7);
    }

    /// @custom:key box
    function storageIndexCopyValue(uint i, uint j) public {
        require(1 < values.length);
        require(i == 5 && j == 1);
        values[1] = 8;
        balances[i] = values[j];
        uint r = balances[5];
        assert(r == 8);
    }

    /// @custom:key box
    function storageIndexCopysourceAfterPush() public {
        require(matrix.length == 0);
        uint[][] storage m = matrix;
        m.push();
        m[0] = values;
        // the .key postcondition compared the whole matrix[0] subtree against values, which has
        // no Solidity form; reading matrix[0].length back does not discharge either, so this
        // only checks that the copy-after-push executes
        assert(matrix.length == 1);
    }

    /// @custom:key box
    function storageIndexDecomposeAfterPush() public {
        require(0 < matrix.length);
        require(matrix[0].length == 0);
        matrix[0].push(100);
        matrix[0][0] = 7;
        uint r = matrix[0][0];
        assert(r == 7);
    }

    function storageIndexDeleteMappingBool() public {
        flags[1] = true;
        delete flags[1];
        bool r = flags[1];
        assert(!r);
    }

    function storageIndexDeleteMappingStruct() public {
        delete people[1];
        assert(people[1].age == 0);
        assert(people[1].account.balance == 0);
    }

    /// @custom:key box
    function storageIndexDeleteNseIndex(uint k) public {
        require(k == 2);
        balances[3] = 7;
        delete balances[k+1];
        uint r = balances[3];
        assert(r == 0);
    }

    /// @custom:key box
    function storageIndexDelete() public {
        require(1 < values.length);
        values[1] = 7;
        delete values[1];
        uint r = values[1];
        assert(r == 0);
    }

    /// @custom:key box
    function storageIndexDivAssign() public {
        require(1 < values.length);
        values[1] = 40;
        values[1] /= 8;
        uint r = values[1];
        assert(r == 5);
    }

    /// @custom:key box
    function storageIndexModAssign() public {
        require(1 < values.length);
        values[1] = 40;
        values[1] %= 6;
        uint r = values[1];
        assert(r == 4);
    }

    /// @custom:key box
    function storageIndexMulAssign() public {
        require(1 < values.length);
        values[1] = 5;
        values[1] *= 6;
        uint r = values[1];
        assert(r == 30);
    }

    /// @custom:key box
    function storageIndexMultipleWrites() public {
        require(3 < values.length);
        values[3] = 5;
        values[3] = 8;
        uint r = values[3];
        assert(r == 8);
    }

    /// @custom:key box
    function storageIndexPostdecrementAssign() public {
        require(1 < values.length);
        values[1] = 40;
        uint r = values[1]--;
        assert(r == 40);
    }

    /// @custom:key box
    function storageIndexPostdecrement() public {
        require(1 < values.length);
        values[1] = 40;
        values[1]--;
        uint r = values[1];
        assert(r == 39);
    }

    /// @custom:key box
    function storageIndexPostincrementAssign() public {
        require(1 < values.length);
        values[1] = 40;
        uint r = values[1]++;
        assert(r == 40);
    }

    /// @custom:key box
    function storageIndexPostincrement() public {
        require(1 < values.length);
        values[1] = 40;
        values[1]++;
        uint r = values[1];
        assert(r == 41);
    }

    /// @custom:key box
    function storageIndexPredecrementAssign() public {
        require(1 < values.length);
        values[1] = 40;
        uint r = --values[1];
        assert(r == 39);
    }

    /// @custom:key box
    function storageIndexPredecrement() public {
        require(1 < values.length);
        values[1] = 40;
        --values[1];
        uint r = values[1];
        assert(r == 39);
    }

    /// @custom:key box
    function storageIndexPreincrementAssign() public {
        require(1 < values.length);
        values[1] = 40;
        uint r = ++values[1];
        assert(r == 41);
    }

    /// @custom:key box
    function storageIndexPreincrement() public {
        require(1 < values.length);
        values[1] = 40;
        ++values[1];
        uint r = values[1];
        assert(r == 41);
    }

    /// @custom:key box
    function storageIndexReadMappingStoreRoot(uint k) public {
        require(k == 1);
        balances[1] = 42;
        total = balances[k];
        uint r = total;
        assert(r == 42);
    }

    /// @custom:key box
    function storageIndexReadNseIndex(uint i) public {
        require(2 < values.length);
        require(i == 1);
        values[2] = 9;
        uint r = values[i+1];
        assert(r == 9);
    }

    /// @custom:key box
    function storageIndexSubAssign() public {
        require(1 < values.length);
        values[1] = 40;
        values[1] -= 8;
        uint r = values[1];
        assert(r == 32);
    }

    /// @custom:key box
    function storageIndexWriteNseChain(uint i, uint x, uint y) public {
        require(i == 2 && x == 3 && y == 4);
        balances[i+1] = x*y + 3;
        uint r = balances[3];
        assert(r == 15);
    }

    function storageLocalDeclSkip() public {
        Person storage p;
        p = alice;
        age = 7;
        uint r = age;
        assert(r == 7);
    }

    /// @custom:key box
    function storageMatrixNseIndex(uint i, uint j, uint x, uint y) public {
        require(2 < matrix.length);
        require(3 < matrix[2].length);
        require(i == 1 && j == 2 && x == 5 && y == 6);
        matrix[i+1][j+1] = x + y;
        assert(matrix[2][3] == 11);
    }

    /// @custom:key box
    function storageMatrixWriteRead() public {
        require(2 < matrix.length);
        require(3 < matrix[2].length);
        matrix[2][3] = 99;
        uint r = matrix[2][3];
        assert(r == 99);
    }

    /// @custom:key box
    function storagePopAfterPush() public {
        require(values.length == 0);
        values.push();
        values.pop();
        assert(values.length == 0);
    }

    /// @custom:key box
    function storagePopNonempty() public {
        require(values.length == 2);
        values.pop();
        assert(values.length == 1);
        // the popped slot is only observable again once it is back in bounds
        values.push();
        assert(values[1] == 0);
    }

    function storagePopUnknownLength() public {
        values.push();
        values.pop();
    }

    /// @custom:key box
    function storagePushEmpty() public {
        require(values.length == 2);
        values.push();
        assert(values.length == 3);
    }

    function storagePushLengthPositive() public {
        values.push();
        assert(values.length > 0);
    }

    /// @custom:key box
    function storagePushLocalBind() public {
        require(persons.length == 2);
        Person storage p;
        p = persons.push();
        assert(persons.length == 3);
    }

    /// @custom:key box
    function storagePushNonsimpleArg(uint x, uint y) public {
        require(values.length == 2);
        require(x == 40 && y == 2);
        values.push(x + y);
        assert(values[2] == 42);
        assert(values.length == 3);
    }

    function storagePushReadBack() public {
        values.push(42);
        uint r = values[values.length - 1];
        assert(r == 42);
    }

    /// @custom:key box
    function storagePushReturnAssign() public {
        require(values.length == 2);
        values.push() = 42;
        assert(values[2] == 42);
        assert(values.length == 3);
    }

    /// @custom:key box
    function storagePushReturnPrimitiveBind() public {
        require(values.length == 2);
        uint y = values.push();
        assert(y == 0);
        assert(values.length == 3);
        assert(values[2] == 0);
    }

    function storageRootAddAssign() public {
        age = 10;
        age += 5;
        uint r = age;
        assert(r == 15);
    }

    function storageRootCopySource() public {
        age = 34;
        balance = age;
        uint r = balance;
        assert(r == 34);
    }

    function storageRootCopyStruct() public {
        bob.age = 7;
        alice = bob;
        uint r = alice.age;
        assert(r == 7);
    }

    function storageRootDeleteStruct() public {
        alice.age = 30;
        delete alice;
        uint r = alice.age;
        assert(r == 0);
    }

    function storageRootDeleteThenCopy() public {
        bob.age = 30;
        delete bob;
        alice = bob;
        uint r = alice.age;
        assert(r == 0);
    }

    function storageRootDelete() public {
        age = 10;
        delete age;
        uint r = age;
        assert(r == 0);
    }

    function storageRootDisjoint() public {
        age = 7;
        balance = 9;
        uint r = age;
        assert(r == 7);
    }

    function storageRootDivAssign() public {
        age = 20;
        age /= 4;
        uint r = age;
        assert(r == 5);
    }

    function storageRootModAssign() public {
        age = 17;
        age %= 5;
        uint r = age;
        assert(r == 2);
    }

    function storageRootMulAssign() public {
        age = 6;
        age *= 3;
        uint r = age;
        assert(r == 18);
    }

    function storageRootMultipleWrites() public {
        age = 1;
        age = 2;
        uint r = age;
        assert(r == 2);
    }

    function storageRootPostdecrementAssign() public {
        age = 10;
        uint r = age--;
        assert(r == 10);
    }

    function storageRootPostincrementAssign() public {
        age = 10;
        uint r = age++;
        assert(r == 10);
    }

    function storageRootPostincrement() public {
        age = 10;
        age++;
        uint r = age;
        assert(r == 11);
    }

    function storageRootPredecrement() public {
        age = 10;
        --age;
        uint r = age;
        assert(r == 9);
    }

    function storageRootPreincrementAssign() public {
        age = 10;
        uint r = ++age;
        assert(r == 11);
    }

    function storageRootPreincrement() public {
        age = 10;
        ++age;
        uint r = age;
        assert(r == 11);
    }

    function storageRootSubAssign() public {
        age = 10;
        age -= 4;
        uint r = age;
        assert(r == 6);
    }

    /// @custom:key box
    function storageRootWriteRhsCapture(uint x, uint y, uint z) public {
        require(x == 1 && y == 2 && z == 3);
        total = x + y*z;
        uint r = total;
        assert(r == 7);
    }

    function storageToMemory() public {
        alice.age = 27;
        Person memory carol = alice;
        alice.age = 30;
        uint r = carol.age;
        assert(r == 27);
    }

    function subtractionSimple() public pure {
        uint r = 7 - 2;
        assert(r == 5);
    }

    function subtractionStorageRead() public {
        alice.age = 10;
        uint r = alice.age - 3;
        assert(r == 7);
    }

    /// @custom:key box
    function unaryMinusSimple(int x) public pure {
        require(x == 5);
        int r = -x;
        // a negative literal directly inside the assert condition does not discharge
        int expected = -5;
        assert(r == expected);
    }

    /// @custom:key box
    function testDeepPopDoesNotResetMappingMember() public {
        require(ledgerUses.length == 0);
        ledgerUses.push();
        ledgerUses[0].ledger.balances[1] = 10;
        ledgerUses.pop();
        ledgerUses.push();
        assert(ledgerUses[0].ledger.balances[1] == 10);
    }

    /// @custom:key box
    function testDeleteArrayDoesNotResetElementMappingMember() public {
        require(ledgerUses.length == 0);
        ledgerUses.push();
        ledgerUses[0].ledger.nonce = 3;
        ledgerUses[0].ledger.balances[1] = 10;
        delete ledgerUses;
        ledgerUses.push();
        assert(ledgerUses[0].ledger.nonce == 0);
        assert(ledgerUses[0].ledger.balances[1] == 10);
    }

    function testMemoryAliasing() public pure {
        Person memory carol;
        Account memory carolAcc = carol.account;
        carolAcc.balance = 100;
        assert(carol.account.balance == 100);
    }

    function testMemoryDeleteAlias() public pure {
        Person memory carol;
        Account memory carolAcc = carol.account;
        carolAcc.balance = 100;
        delete carolAcc;
        uint b = carolAcc.balance;
        assert(b == 0);
    }

    function testMemoryDeleteIdentityFieldFreshensSlot() public pure {
        Person memory carol;
        Account memory carolAcc = carol.account;
        carolAcc.balance = 100;
        delete carol.account;
        assert(carol.account.balance == 0);
        assert(carolAcc.balance == 100);
    }

    function testMemoryDeletePrimitiveField() public pure {
        Person memory carol;
        carol.age = 20;
        delete carol.age;
        assert(carol.age == 0);
    }

    function testMemoryEvaluationOrder() public pure {
        uint[] memory xs = new uint[](3);
        uint i = 0;
        xs[++i] = ++i;
        assert(i == 2);
        assert(xs[2] == 1);
    }

    function testMemoryFieldShallowCopy() public pure {
        Person memory carol;
        Person memory david;
        david.account.balance = 50;
        carol.account = david.account;
        carol.account.balance = 60;
        assert(david.account.balance == 60);
        assert(carol.account.balance == 60);
    }

    function testMemoryIndexWriteImpureIndexPrimitiveRhs() public pure {
        uint[] memory xs = new uint[](2);
        uint i = 0;
        xs[i++] = i;
        assert(i == 1);
        assert(xs[0] == 0);
    }

    function testMemoryIndexWriteImpureIndexRefRhs() public pure {
        Token[] memory toks = new Token[](2);
        Token memory tmp;
        tmp.value = 5;
        uint j = 0;
        toks[j++] = tmp;
        assert(j == 1);
        assert(toks[0].value == 5);
    }

    function testMemoryRootAlias() public pure {
        Person memory carol;
        Person memory david;
        david.age = 40;
        carol = david;
        carol.age = 41;
        assert(david.age == 41);
        assert(carol.age == 41);
    }

    function testMemoryRootDeleteRebindsOnlyLocal() public pure {
        Person memory carol;
        Person memory carolAlias = carol;
        carol.age = 33;
        delete carol;
        assert(carol.age == 0);
        assert(carolAlias.age == 33);
    }

    function testMemoryToStorageCopyComplexSource() public {
        Person memory carol;
        carol.account.balance = 50;
        alice.account = carol.account;
        carol.account.balance = 51;
        assert(alice.account.balance == 50);
    }

    function testMemoryToStorageCopyComplexTarget() public {
        Token memory carolToken;
        carolToken.value = 99;
        alice.account.token = carolToken;
        carolToken.value = 100;
        assert(alice.account.token.value == 99);
    }

    function testMemoryToStorageCopyField() public {
        Account memory carolAcc;
        carolAcc.balance = 50;
        alice.account = carolAcc;
        carolAcc.balance = 51;
        assert(alice.account.balance == 50);
    }

    function testMemoryToStorageCopyRoot() public {
        Person memory carol;
        carol.age = 42;
        alice = carol;
        carol.age = 43;
        assert(alice.age == 42);
    }

    /// @custom:key box
    function testMemoryToStorageIndexCopyImpureIndex() public {
        require(persons.length == 0);
        persons.push();
        persons.push();
        Person memory carol;
        carol.age = 7;
        uint i = 0;
        persons[i++] = carol;
        assert(i == 1);
        assert(persons[0].age == 7);
    }

    function testMemoryTokenArrayAuxiliaryCases() public pure {
        Token[] memory carolTokens = new Token[](3);
        Token[] memory davidTokens = new Token[](3);
        uint i = 0;
        uint j = 0;
        Token memory tmp;
        tmp.value = 7;
        davidTokens[j] = tmp;
        carolTokens[++i] = davidTokens[j];
        Token memory carolTok = carolTokens[i];
        carolTok.value = 9;
        delete carolTokens[i];
        assert(carolTok.value == 9);
        assert(carolTokens[1].value == 0);
    }

    function testMemoryUintArrayAuxiliaryCases() public pure {
        uint[] memory carolValues = new uint[](3);
        uint i = 0;
        carolValues[++i] = 77;
        uint v = carolValues[i];
        delete carolValues[i];
        assert(v == 77);
        assert(carolValues[1] == 0);
    }

    function testMemoryUintArrayPostdecrement() public pure {
        uint[] memory carolValues = new uint[](3);
        uint i = 1;
        carolValues[i--] = 77;
        uint v = carolValues[1];
        delete carolValues[1];
        assert(i == 0);
        assert(v == 77);
        assert(carolValues[1] == 0);
    }

    function testMemoryUintArrayPostincrement() public pure {
        uint[] memory carolValues = new uint[](3);
        uint i = 0;
        carolValues[i++] = 77;
        uint v = carolValues[0];
        delete carolValues[0];
        assert(i == 1);
        assert(v == 77);
        assert(carolValues[0] == 0);
    }

    function testMemoryUintArrayPredecrement() public pure {
        uint[] memory carolValues = new uint[](3);
        uint i = 1;
        carolValues[--i] = 77;
        uint v = carolValues[i];
        delete carolValues[i];
        assert(i == 0);
        assert(v == 77);
        assert(carolValues[0] == 0);
    }

    /// @custom:key box
    function testNestedIndexWriteImpureIndexPrimitiveRhs() public {
        require(matrix.length == 0);
        matrix.push();
        matrix.push();
        matrix[1].push(100);
        uint i = 1;
        matrix[i++][0] = i;
        assert(i == 2);
        assert(matrix[1][0] == 1);
    }

    /// @custom:key box
    function testNestedIndexReadImpureIndex() public {
        require(matrix.length == 0);
        matrix.push();
        matrix.push();
        require(matrix[1].length == 0);
        matrix[1].push(100);
        uint i = 1;
        uint v = matrix[i++][0];
        assert(i == 2);
        assert(v == 100);
    }

    /// @custom:key box
    function testNestedIndexWriteImpureReceiverAndIndex() public {
        require(matrix.length == 0);
        matrix.push();
        matrix.push();
        require(matrix[0].length == 0);
        require(matrix[1].length == 0);
        matrix[0].push(0);
        matrix[0].push(0);
        matrix[1].push(0);
        matrix[1].push(0);
        uint i = 0;
        matrix[i++][i++] = 77;
        assert(i == 2);
        assert(matrix[0][1] == 77);
        assert(matrix[1][0] == 0);
    }

    /// @custom:key box
    function testNestedIndexReadImpureReceiverAndIndex() public {
        require(matrix.length == 0);
        matrix.push();
        matrix.push();
        require(matrix[0].length == 0);
        matrix[0].push(0);
        matrix[0].push(11);
        matrix[1].push(22);
        uint i = 0;
        uint v = matrix[i++][i++];
        assert(i == 2);
        assert(v == 11);
    }

    /// @custom:key box
    function testStorageDeleteImpureReceiver() public {
        require(matrix.length == 0);
        matrix.push();
        matrix.push();
        matrix[0].push(9);
        uint i = 0;
        delete matrix[i++][0];
        assert(i == 1);
        assert(matrix[0][0] == 0);
    }

    /// @custom:key box
    function testStoragePushImpureReceiver() public {
        require(matrix.length == 0);
        matrix.push();
        matrix.push();
        require(matrix[0].length == 0);
        uint i = 0;
        matrix[i++].push(i);
        assert(i == 1);
        assert(matrix[0][0] == 1);
    }

    /// @custom:key box
    function testCompoundAssignImpureReceiver() public {
        require(persons.length == 0);
        persons.push();
        persons.push();
        persons[0].age = 5;
        uint i = 0;
        persons[i++].age += i;
        assert(i == 1);
        assert(persons[0].age == 5);
    }

    function testMemoryFieldWriteImpureReceiver() public pure {
        Token[] memory toks = new Token[](2);
        uint i = 0;
        toks[i++].value = i;
        assert(i == 1);
        assert(toks[0].value == 0);
    }

    /// @custom:key box
    function testIndexWriteReceiverReadsMutatedVar() public {
        require(matrix.length == 0);
        matrix.push();
        matrix.push();
        require(matrix[0].length == 0);
        require(matrix[1].length == 0);
        matrix[0].push(0);
        matrix[1].push(0);
        uint k = 0;
        matrix[k][k++] = 77;
        assert(k == 1);
        assert(matrix[0][0] == 77);
        assert(matrix[1][0] == 0);
    }

    function testNestedStorageWrites() public {
        alice.account.balance = 10;
        alice.account.token.value = 5;
        uint b = alice.account.balance;
        uint v = alice.account.token.value;
        assert(b == 10);
        assert(v == 5);
    }

    function testStorageAliases() public {
        Person storage p = alice;
        Account storage acc = p.account;
        acc.balance = 100;
        p.account.token.value = 3;
        assert(alice.account.balance == 100);
        assert(alice.account.token.value == 3);
    }

    /// @custom:key box
    function testStorageArrayReadWrite() public {
        require(tokens.length == 0);
        tokens.push();
        tokens[0].value = 100;
        uint v = tokens[0].value;
        assert(v == 100);
    }

    /// @custom:key box
    function testStorageComplexReceiverPushFieldLvalue() public {
        require(bucket.tokens.length == 0);
        bucket.tokens.push().value = 5;
        Token[] storage bt = bucket.tokens;
        assert(bt.length == 1);
        assert(bt[0].value == 5);
    }

    /// @custom:key box
    function testStorageComplexReceiverPushLvalueCopy() public {
        require(bucket.tokens.length == 0);
        alice.account.token.value = 7;
        Token storage tokRef = alice.account.token;
        bucket.tokens.push() = tokRef;
        Token[] storage bt = bucket.tokens;
        assert(bt.length == 1);
        assert(bt[0].value == 7);
    }

    function testStorageDeletePaperCase() public {
        alice.account.balance = 100;
        alice.account.token.value = 7;
        delete alice.account;
        uint b = alice.account.balance;
        uint v = alice.account.token.value;
        assert(b == 0);
        assert(v == 0);
    }

    /// @custom:key box
    function testStorageIndexWriteImpureIndexPrimitiveRhs() public {
        require(a.length == 0);
        uint i = 0;
        a.push(100);
        a.push(100);
        a[i++] = i;
        assert(i == 1);
        assert(a[0] == 0);
    }

    /// @custom:key box
    function testStorageIndexWriteImpureIndexRefRhs() public {
        require(persons.length == 0);
        persons.push();
        persons.push();
        bob.age = 0;
        persons[bob.age++] = bob;
        assert(bob.age == 1);
        assert(persons[0].age == 1);
    }

    /// @custom:key box
    function testStorageEvaluationOrder() public {
        require(a.length == 0);
        uint i = 0;
        a.push(100);
        a.push(100);
        a.push(100);
        a[++i] = ++i;
        assert(a[2] == 1);
    }

    function testStorageFieldDeepCopy() public {
        bob.account.balance = 10;
        bob.account.token.value = 7;
        Account storage bobAcc = bob.account;
        alice.account = bobAcc;
        bob.account.balance = 20;
        bob.account.token.value = 9;
        assert(alice.account.balance == 10);
        assert(alice.account.token.value == 7);
    }

    function testStorageMapReadWriteAndDelete() public {
        valuesMap[1] = 10;
        valuesMap[2] = 20;
        uint v = valuesMap[1];
        uint kept = valuesMap[2];
        delete valuesMap[1];
        assert(v == 10);
        assert(kept == 20);
        assert(valuesMap[1] == 0);
        assert(valuesMap[2] == 20);
    }

    function testStorageMapStructCopy() public {
        accountMap[1].balance = 10;
        accountMap[1].token.value = 7;
        accountMap[2] = accountMap[1];
        accountMap[1].balance = 20;
        accountMap[1].token.value = 9;
        assert(accountMap[2].balance == 10);
        assert(accountMap[2].token.value == 7);
    }

    /// @custom:key box
    function testStorageNestedPushReturnAlias() public {
        require(persons.length == 0);
        Account storage acc = persons.push().account;
        acc.balance = 50;
        assert(persons.length == 1);
        assert(acc.balance == 50);
    }

    /// @custom:key box
    function testStoragePushFieldLvalue() public {
        require(tokens.length == 0);
        tokens.push().value = 11;
        assert(tokens.length == 1);
        assert(tokens[0].value == 11);
    }

    /// @custom:key box
    function testStoragePushLvalueCopiesStorageSource() public {
        require(tokens.length == 0);
        alice.account.token.value = 9;
        Token storage storageRef = alice.account.token;
        tokens.push() = storageRef;
        assert(tokens.length == 1);
        assert(tokens[0].value == 9);
    }

    /// @custom:key box
    function testStoragePushLvaluePrimitive() public {
        require(values.length == 0);
        values.push() = 77;
        assert(values.length == 1);
        assert(values[0] == 77);
    }

    /// @custom:key box
    function testStoragePushReturnAlias() public {
        require(tokens.length == 0);
        Token storage t = tokens.push();
        t.value = 99;
        assert(tokens.length == 1);
        assert(tokens[0].value == 99);
    }

    function testArrayCopyClearsOldElements() public {
        delete tokens;
        tokens.push();
        Token storage r = tokens[0];
        tokens.pop();
        r.value = 5;
        delete bucket.tokens;
        bucket.tokens.push();
        bucket.tokens[0].value = 7;
        bucket.tokens = tokens;
        bucket.tokens.push();
        assert(bucket.tokens[0].value == 0);
    }

    /// @custom:key box
    function testStorageIndexDeleteOutOfBoundsReverts() public {
        delete values;
        delete values[0];
        assert(false);
    }

    /// @custom:key box
    function testFixedArrayDeleteKeepsLength() public {
        require(2 < fixedValues.length);
        fixedValues[1] = 7;
        delete fixedValues;
        assert(2 < fixedValues.length);
        assert(fixedValues[1] == 0);
    }

    function testFixedArrayLength() public view {
        assert(fixedValues.length == 3);
    }

    function testFixedArrayIndexInBounds() public {
        fixedValues[2] = 1;
        assert(fixedValues[2] == 1);
    }

    function testFixedStructArrayLength() public view {
        assert(fixedTokens.length == 2);
    }

    function testStructFixedMemberLength() public view {
        assert(triple.items.length == 3);
    }

    function testMemoryStructFixedMemberLength() public pure {
        Triple memory t;
        assert(t.items.length == 3);
        t.items[1] = 5;
        assert(t.items[1] == 5);
        assert(t.items[0] == 0);
    }

    /// @custom:key box
    function testFixedElementOfDynamicArrayLength() public view {
        require(0 < rows.length);
        assert(rows[0].length == 3);
    }

    function testMemoryFixedArrayLength() public pure {
        uint[3] memory x;
        assert(x.length == 3);
        x[1] = 5;
        assert(x[1] == 5);
        assert(x[0] == 0);
    }

    function testMemoryNestedFixedArrayLength() public pure {
        uint[2][3] memory y;
        assert(y.length == 3);
        assert(y[0].length == 2);
    }

    function testNewArrayOfFixedElementLength() public pure {
        uint[2][] memory z = new uint[2][](4);
        assert(z.length == 4);
        assert(z[1].length == 2);
    }

    function testMappingOfFixedArrayLength(uint k) public view {
        assert(fixedByKey[k].length == 3);
    }

    function testMemoryDynamicArrayDefaultLength() public pure {
        uint[] memory d;
        assert(d.length == 0);
    }

    /// @custom:key box
    function testFixedStructArrayDeleteResetsElements() public {
        require(1 < fixedTokens.length);
        fixedTokens[1].value = 7;
        delete fixedTokens;
        assert(1 < fixedTokens.length);
        assert(fixedTokens[1].value == 0);
    }

    /// @custom:key box
    function testStructWithFixedArrayDeleteKeepsLength() public {
        require(2 < triple.items.length);
        triple.items[1] = 7;
        triple.tag = 3;
        delete triple;
        assert(2 < triple.items.length);
        assert(triple.items[1] == 0);
        assert(triple.tag == 0);
    }

    /// @custom:key box
    function testStructWithFixedArrayCopy() public {
        require(2 < triple.items.length);
        triple.items[1] = 7;
        triple2 = triple;
        assert(triple2.items[1] == 7);
    }

    /// @custom:key box
    function testFixedMappingArrayDeleteKeepsEntries() public {
        require(1 < fixedMaps.length);
        fixedMaps[1][2] = 5;
        delete fixedMaps;
        assert(fixedMaps[1][2] == 5);
    }

    function testPopKeepsMappingElementEntries() public {
        delete mapArray;
        mapArray.push();
        mapArray[0][1] = 5;
        mapArray.pop();
        mapArray.push();
        assert(mapArray[0][1] == 5);
    }

    function testDeleteKeepsMappingElementEntries() public {
        delete mapArray;
        mapArray.push();
        mapArray[0][1] = 5;
        delete mapArray;
        mapArray.push();
        assert(mapArray[0][1] == 5);
    }

    function testPushBindMappingElement() public {
        delete mapArray;
        mapping(uint => uint) storage m = mapArray.push();
        m[1] = 4;
        assert(mapArray[0][1] == 4);
    }

    function testStorageRootDeepCopy() public {
        bob.age = 21;
        bob.account.balance = 11;
        alice = bob;
        bob.age = 30;
        bob.account.balance = 12;
        assert(alice.age == 21);
        assert(alice.account.balance == 11);
    }

    function testStorageStructDeleteSkipsMappingMember() public {
        ledger.nonce = 5;
        ledger.balances[1] = 10;
        ledger.balances[2] = 20;
        delete ledger;
        assert(ledger.nonce == 0);
        assert(ledger.balances[1] == 10);
        assert(ledger.balances[2] == 20);
        delete ledger.balances[1];
        assert(ledger.balances[1] == 0);
        assert(ledger.balances[2] == 20);
    }

    function testStorageToMemoryCopyComplexPath() public {
        alice.account.token.value = 17;
        Token memory t = alice.account.token;
        alice.account.token.value = 18;
        assert(t.value == 17);
    }

    function testStorageToMemoryCopyField() public {
        alice.account.balance = 10;
        Account memory acc = alice.account;
        alice.account.balance = 20;
        uint v = acc.balance;
        assert(v == 10);
    }

    function testStorageToMemoryCopyRoot() public {
        alice.age = 25;
        Person memory carol = alice;
        alice.age = 30;
        uint v = carol.age;
        assert(v == 25);
    }

    function testStorageWriteAndRead() public {
        uint x = 20;
        uint y = 1;
        alice.age = x + y;
        uint v = alice.age;
        assert(v == 21);
    }

    // ── split: one function per modality ──

    function storageFieldDecomposition() public {
        alice.account.balance = 34;
        assert(alice.account.balance == 34);
        uint r = alice.account.balance;
        assert(r == 34);
    }

    function storageFieldDeepValue() public {
        alice.account.token.value = 7;
        assert(alice.account.token.value == 7);
        uint r = alice.account.token.value;
        assert(r == 7);
    }

    /// @custom:key box
    function storageIndexDecomposition() public {
        require(2 < matrix.length);
        require(3 < matrix[2].length);
        matrix[2][3] = 34;
        assert(matrix[2][3] == 34);
        uint r = matrix[2][3];
        assert(r == 34);
    }

    /// @custom:key box
    function storageIndexRootArray() public {
        require(1 < values.length);
        values[1] = 42;
        assert(values[1] == 42);
        uint r = values[1];
        assert(r == 42);
    }

    // ── shared: both conjuncts run the same program ──

    function storageFieldDisjointFields() public {
        alice.account.balance = 1;
        alice.account.token.value = 2;
        assert(alice.account.balance == 1);
        assert(alice.account.token.value == 2);
    }

    function storageFieldDisjointRoots() public {
        alice.age = 1;
        bob.age = 2;
        assert(alice.age == 1);
        assert(bob.age == 2);
    }

    // ── several observations: asserted in the body ──

    function memoryAssignForms() public {
        alice.age = 27;
        Person memory carol;
        carol = alice;
        alice.age = 30;
        uint r1 = carol.age;
        uint[] memory xs;
        xs = new uint[](4);
        xs[1] = 33;
        uint r2 = xs[1];
        assert(r1 == 27);
        assert(r2 == 33);
    }

    function memoryDelete() public pure {
        Person memory carol;
        Account memory acc = carol.account;
        carol.age = 20;
        acc.balance = 100;
        delete carol.age;
        delete carol.account;
        uint result = carol.age;
        uint aliasBalance = acc.balance;
        uint newBalance = carol.account.balance;
        assert(result == 0);
        assert(aliasBalance == 100);
        assert(newBalance == 0);
    }

    function storageAliasRebindOriginal() public {
        uint before = alice.age;
        Person storage alicePath = alice;
        bob.age = 20;
        alicePath = bob;
        assert(alice.age == before);
    }

    function testSimpleAssert() public {
        age = 42;
        uint v = age;
        assert(v == 42);
    }

    // ── arithmetic on pinned ranges ──

    /// @custom:key box
    function localArithmeticInRange(uint x) public pure {
        require(x >= 1 && x <= 100);
        uint r;
        r = x + 1;
        r -= 1;
        ++r;
        assert(r == x + 1);
    }

    /// @custom:key box
    function signedUnaryMinusInRange(int8 x) public pure {
        require(x == 5);
        int8 r;
        int8 expected;
        r = -x;
        expected = -5;
        assert(r == expected);
    }

    // ── Reference-source evaluation order ──

    /// @custom:key box
    function storageIndexWriteRefSourceImpureIndex() public {
        require(persons.length == 0);
        persons.push();
        Person memory p;
        persons[p.age++] = p;
        assert(persons[0].age == 1);
    }

    /// @custom:key box
    function storageFieldWriteRefSourceImpureReceiver() public {
        require(persons.length == 0);
        persons.push();
        Account memory acc;
        persons[acc.balance++].account = acc;
        assert(persons[0].account.balance == 1);
    }

    /// @custom:key box
    function storageFieldWriteStorageRefImpureReceiver() public {
        require(persons.length == 0);
        persons.push();
        persons.push();
        alice.account.balance = 9;
        Account storage src = alice.account;
        uint i = 0;
        persons[i++].account = src;
        assert(i == 1);
        assert(persons[0].account.balance == 9);
    }

    /// @custom:key box
    function storageFieldWriteRootRefImpureReceiver() public {
        require(persons.length == 0);
        persons.push();
        persons.push();
        tok.value = 4;
        uint i = 0;
        persons[i++].account.token = tok;
        assert(i == 1);
        assert(persons[0].account.token.value == 4);
    }

    function memoryFieldWriteMemRefImpureReceiver() public pure {
        Person[] memory ps = new Person[](2);
        Account memory src;
        src.balance = 6;
        uint i = 0;
        ps[i++].account = src;
        assert(i == 1);
        assert(ps[0].account.balance == 6);
    }

    /// @custom:key box
    function storageIndexWriteRootRefImpureReceiver() public {
        require(buckets.length == 0);
        buckets.push();
        buckets.push();
        require(buckets[1].tokens.length == 0);
        buckets[1].tokens.push();
        tok.value = 3;
        uint i = 1;
        buckets[i++].tokens[0] = tok;
        assert(i == 2);
        assert(buckets[1].tokens[0].value == 3);
    }

    /// @custom:key box
    function storageIndexWriteStorageRefImpureReceiver() public {
        require(buckets.length == 0);
        buckets.push();
        buckets.push();
        require(buckets[1].tokens.length == 0);
        buckets[1].tokens.push();
        tok.value = 8;
        Token storage src = tok;
        uint i = 1;
        buckets[i++].tokens[0] = src;
        assert(i == 2);
        assert(buckets[1].tokens[0].value == 8);
    }

    /// @custom:key box
    function memoryToStorageIndexImpureReceiver() public {
        require(buckets.length == 0);
        buckets.push();
        buckets.push();
        require(buckets[1].tokens.length == 0);
        buckets[1].tokens.push();
        Token memory src;
        src.value = 5;
        uint i = 1;
        buckets[i++].tokens[0] = src;
        assert(i == 2);
        assert(buckets[1].tokens[0].value == 5);
    }

    function memoryIndexWriteMemRefImpureReceiver() public pure {
        TokenBucket[] memory tbs = new TokenBucket[](2);
        Token[] memory slots = new Token[](2);
        tbs[1].tokens = slots;
        Token memory src;
        src.value = 2;
        uint i = 1;
        tbs[i++].tokens[0] = src;
        assert(i == 2);
        assert(tbs[1].tokens[0].value == 2);
    }

    // ── Binary operand evaluation order: solc evaluates the right operand first ──

    function additionLeftImpureRightReadFirst() public pure {
        uint i = 1;
        uint x = i++ + i;
        assert(x == 2);
        assert(i == 2);
    }

    function additionRightImpure() public pure {
        uint i = 1;
        uint x = i + i++;
        assert(x == 3);
        assert(i == 2);
    }

    function additionBothOperandsImpure() public pure {
        uint i = 1;
        uint x = i++ + i++;
        assert(x == 3);
        assert(i == 3);
    }

    function subtractionLeftImpureRightReadFirst() public pure {
        uint i = 5;
        uint x = i++ - i;
        assert(x == 0);
        assert(i == 6);
    }

    function lessThanLeftImpureRightReadFirst() public pure {
        uint i = 1;
        bool b = i++ < i;
        assert(!b);
        assert(i == 2);
    }

    // ── Storage copy: mapping members stay the target's own ──

    function testCopyRootKeepsValueMembers() public {
        bob.age = 7;
        bob.account.balance = 3;
        alice = bob;
        bob.age = 8;
        assert(alice.age == 7);
        assert(alice.account.balance == 3);
    }

    function testCopyFieldNested() public {
        Account storage acc = bob.account;
        acc.token.value = 5;
        alice.account = acc;
        acc.token.value = 6;
        assert(alice.account.token.value == 5);
    }

    /// @custom:key box
    function testCopyOfCopy() public {
        require(persons.length == 0);
        bob.age = 4;
        alice = bob;
        persons.push();
        persons[0] = alice;
        assert(persons[0].age == 4);
    }

    /// @custom:key box
    function testCopyIntoMappingEntry(uint k) public {
        require(k == 3);
        alice.age = 6;
        people[k] = alice;
        alice.age = 7;
        assert(people[k].age == 6);
    }

    /// @custom:key box
    function testCopyArrayMemberElements() public {
        require(basketA.items.length == 0);
        require(basketB.items.length == 0);
        basketA.items.push(9);
        basketB = basketA;
        basketA.items[0] = 1;
        assert(basketB.items.length == 1);
        assert(basketB.items[0] == 9);
    }

    function testCopyPrimitiveRoot() public {
        age = 3;
        balance = age;
        age = 4;
        assert(balance == 3);
    }

    function testCopyStoreRootFromField() public {
        alice.account.token.value = 2;
        tok = alice.account.token;
        alice.account.token.value = 1;
        assert(tok.value == 2);
    }

    function testCopyStoreRootFromIndex() public {
        people[1].age = 2;
        alice = people[1];
        people[1].age = 3;
        assert(alice.age == 2);
    }

    /// @custom:key box
    function testPushCopyThenDeleteTarget() public {
        require(tokens.length == 0);
        tok.value = 4;
        Token storage src = tok;
        tokens.push() = src;
        delete tokens[0];
        assert(tokens[0].value == 0);
        assert(tok.value == 4);
    }

    // ── Index writes whose receiver and index are both impure (docs/storage.md section 5) ──

    /// @custom:key box
    function indexWriteBothImpureStorageRef() public {
        require(buckets.length == 0);
        buckets.push();
        buckets.push();
        require(buckets[1].tokens.length == 0);
        buckets[1].tokens.push();
        buckets[1].tokens.push();
        tok.value = 8;
        Token storage src = tok;
        uint i = 1;
        uint j = 0;
        buckets[i++].tokens[j++] = src;
        assert(i == 2);
        assert(j == 1);
        assert(buckets[1].tokens[0].value == 8);
    }

    /// @custom:key box
    function indexWriteBothImpureMemToStorage() public {
        require(buckets.length == 0);
        buckets.push();
        buckets.push();
        require(buckets[1].tokens.length == 0);
        buckets[1].tokens.push();
        buckets[1].tokens.push();
        Token memory src;
        src.value = 5;
        uint i = 1;
        uint j = 0;
        buckets[i++].tokens[j++] = src;
        assert(i == 2);
        assert(j == 1);
        assert(buckets[1].tokens[0].value == 5);
    }

    function indexWriteBothImpureMemoryValue() public pure {
        Basket[] memory bs = new Basket[](2);
        uint[] memory slots = new uint[](2);
        bs[1].items = slots;
        uint i = 1;
        uint j = 0;
        bs[i++].items[j++] = 42;
        assert(i == 2);
        assert(j == 1);
        assert(bs[1].items[0] == 42);
    }

    function indexWriteBothImpureMemRef() public pure {
        TokenBucket[] memory tbs = new TokenBucket[](2);
        Token[] memory slots = new Token[](2);
        tbs[1].tokens = slots;
        Token memory src;
        src.value = 2;
        uint i = 1;
        uint j = 0;
        tbs[i++].tokens[j++] = src;
        assert(i == 2);
        assert(j == 1);
        assert(tbs[1].tokens[0].value == 2);
    }

    // ── Mapping indices: nesting, aliases and memory keys ──

    function nestedMappingWriteRead() public {
        grid[1][2] = 7;
        uint r = grid[1][2];
        assert(r == 7);
    }

    function nestedMappingRowAlias() public {
        mapping(uint => uint) storage row = grid[1];
        row[2] = 5;
        uint r = grid[1][2];
        assert(r == 5);
    }

    function arrayOfMappingsIndex() public {
        mapArray.push();
        mapArray[0][1] = 2;
        uint r = mapArray[0][1];
        assert(r == 2);
    }

    function mappingOfLedgerMember() public {
        ledgerMap[1].nonce = 4;
        ledgerMap[1].balances[2] = 3;
        uint n = ledgerMap[1].nonce;
        uint r = ledgerMap[1].balances[2];
        assert(n == 4);
        assert(r == 3);
    }

    function mappingPointerTernary() public {
        flag = true;
        mapping(uint => uint) storage ptr = flag ? balances : valuesMap;
        ptr[1] = 2;
        uint r = balances[1];
        assert(r == 2);
    }

    function mappingReadAsKey() public {
        balances[1] = 3;
        balances[3] = 9;
        uint r = balances[balances[1]];
        assert(r == 9);
    }

    function memoryFieldAsMappingKey() public {
        Person memory carol;
        carol.age = 3;
        balances[carol.age] = 7;
        uint r = balances[3];
        assert(r == 7);
    }

    function mappingEntryThroughMemoryToMappingEntry() public {
        people[1].age = 3;
        Person memory p = people[1];
        people[2] = p;
        people[1].age = 4;
        uint r = people[2].age;
        assert(r == 3);
    }

    function boolKeyMapping() public {
        boolKeyed[true] = 1;
        boolKeyed[false] = 2;
        uint r = boolKeyed[true];
        uint s = boolKeyed[false];
        assert(r == 1);
        assert(s == 2);
    }

    function boolIsTrueOrFalse(bool b) public pure {
        bool x = b == true;
        bool y = b == false;
        assert(x || y);
    }

    function boolKeyMappingSymbolicKey(bool b) public {
        boolKeyed[true] = 1;
        boolKeyed[false] = 2;
        uint r = boolKeyed[b];
        assert(r == 1 || r == 2);
    }

    function recursiveStructMapping() public {
        mapping(uint => Tree) storage kids = tree.kids;
        Tree storage child = kids[0];
        tree.v = 1;
        child.v = 2;
        mapping(uint => Tree) storage grandKids = child.kids;
        grandKids[3].v = 4;
        assert(tree.v == 1);
        assert(kids[0].v == 2);
        assert(grandKids[3].v == 4);
    }

    // ── Number literals ──

    function numberLiteralForms() public pure {
        uint h = 0xff;
        uint u = 1_000;
        uint e = 2e3;
        uint g = 1 gwei;
        uint d = 2 days;
        assert(h == 255);
        assert(u == 1000);
        assert(e == 2000);
        assert(g == 1000000000);
        assert(d == 172800);
    }

    // ── Taclet coverage: one function per taclet no other example applies ──

    function localAddAssign() public pure {
        uint x = 40;
        x += 2;
        assert(x == 42);
    }

    function localMulAssign() public pure {
        uint x = 7;
        x *= 6;
        assert(x == 42);
    }

    function localDivAssign() public pure {
        uint x = 40;
        x /= 8;
        assert(x == 5);
    }

    function localModAssign() public pure {
        uint x = 40;
        x %= 7;
        assert(x == 5);
    }

    function localPostincrement() public pure {
        uint x = 40;
        x++;
        assert(x == 41);
    }

    function localPreincrementAssign() public pure {
        uint x = 40;
        uint r = 0;
        r = ++x;
        assert(r == 41);
        assert(x == 41);
    }

    function localPostdecrement() public pure {
        uint x = 40;
        x--;
        assert(x == 39);
    }

    function localPredecrement() public pure {
        uint x = 40;
        --x;
        assert(x == 39);
    }

    function localDeclPostdecrement() public pure {
        uint x = 40;
        uint r = x--;
        assert(r == 40);
        assert(x == 39);
    }

    function localDeclPredecrement() public pure {
        uint x = 40;
        uint r = --x;
        assert(r == 39);
        assert(x == 39);
    }

    function subAssignValueRhsCapture() public pure {
        uint x = 40;
        uint y = 1;
        x -= y + 1;
        assert(x == 38);
    }

    function mulAssignValueRhsCapture() public pure {
        uint x = 7;
        uint y = 5;
        x *= y + 1;
        assert(x == 42);
    }

    function divAssignValueRhsCapture() public pure {
        uint x = 40;
        uint y = 7;
        x /= y + 1;
        assert(x == 5);
    }

    function modAssignValueRhsCapture() public pure {
        uint x = 40;
        uint y = 6;
        x %= y + 1;
        assert(x == 5);
    }

    function indexWriteValueRhsCapture() public pure {
        uint[] memory xs = new uint[](2);
        uint y = 4;
        xs[1] = y + 1;
        uint r = xs[1];
        assert(r == 5);
    }

    function memoryIndexWriteMemRefRhsCapture() public pure {
        Token[] memory ts = new Token[](2);
        Person memory carol;
        carol.account.token.value = 7;
        ts[0] = carol.account.token;
        uint r = ts[0].value;
        assert(r == 7);
    }

    function memoryIndexDeleteNonSimpleIndexCapture() public pure {
        uint[] memory xs = new uint[](3);
        uint i = 0;
        xs[1] = 5;
        delete xs[i + 1];
        uint r = xs[1];
        assert(r == 0);
    }

    function boolInequalityCaptureLhs() public pure {
        bool b = true;
        bool r = !b != b;
        assert(r);
    }

    function boolInequalityCaptureRhs() public pure {
        bool b = true;
        bool r = b != !b;
        assert(r);
    }

    function greaterThanCaptureRhs() public pure {
        uint x = 3;
        bool r = x > x - 1;
        assert(r);
    }

    function greaterEqualCaptureLhs() public pure {
        uint x = 3;
        bool r = x + 1 >= x;
        assert(r);
    }

    function greaterEqualCaptureRhs() public pure {
        uint x = 3;
        bool r = x >= x - 1;
        assert(r);
    }

    function lessEqualCaptureLhs() public pure {
        uint x = 3;
        bool r = x - 1 <= x;
        assert(r);
    }

    function lessEqualCaptureRhs() public pure {
        uint x = 3;
        bool r = x <= x + 1;
        assert(r);
    }

    function logicalNotCapture() public pure {
        uint x = 3;
        bool r = !(x == 4);
        assert(r);
    }

    function unaryMinusCapture() public pure {
        int x = 3;
        int r = -(x + 1);
        assert(r == -4);
    }

    function multiplicationUnfoldLeft() public pure {
        uint x = 5;
        uint y = 7;
        uint r = (x + 1) * y;
        assert(r == 42);
    }

    function multiplicationUnfoldRight() public pure {
        uint x = 7;
        uint y = 5;
        uint r = x * (y + 1);
        assert(r == 42);
    }

    function divisionUnfoldLeft() public pure {
        uint x = 39;
        uint y = 8;
        uint r = (x + 1) / y;
        assert(r == 5);
    }

    function divisionUnfoldRight() public pure {
        uint x = 40;
        uint y = 7;
        uint r = x / (y + 1);
        assert(r == 5);
    }

    function moduloUnfoldLeft() public pure {
        uint x = 39;
        uint y = 7;
        uint r = (x + 1) % y;
        assert(r == 5);
    }

    function moduloUnfoldRight() public pure {
        uint x = 40;
        uint y = 6;
        uint r = x % (y + 1);
        assert(r == 5);
    }

    function signedDivisionTruncates() public pure {
        int n = -7;
        int b = -2;
        int q1 = n / 2;
        int q2 = 7 / b;
        int q3 = n / b;
        int minusThree = -3;
        assert(q1 == minusThree);
        assert(q2 == minusThree);
        assert(q3 == 3);
    }

    function signedModuloTakesDividendSign() public pure {
        int n = -7;
        int b = -2;
        int r1 = n % 2;
        int r2 = 7 % b;
        int r3 = n % b;
        int minusOne = -1;
        assert(r1 == minusOne);
        assert(r2 == 1);
        assert(r3 == minusOne);
    }

    function storageSignedDivModAssign() public {
        int start = -7;
        signedTotal = start;
        signedTotal /= 2;
        int q = signedTotal;
        int minusThree = -3;
        assert(q == minusThree);
        signedTotal = start;
        signedTotal %= 2;
        int r = signedTotal;
        int minusOne = -1;
        assert(r == minusOne);
    }

    function powerUnfoldLeft() public pure {
        uint x = 1;
        uint y = 3;
        uint r = (x + 1) ** y;
        assert(r == 8);
    }

    function powerUnfoldRight() public pure {
        uint x = 2;
        uint y = 2;
        uint r = x ** (y + 1);
        assert(r == 8);
    }

    function subtractionUnfoldRight() public pure {
        uint x = 40;
        uint y = 1;
        uint r = x - (y + 1);
        assert(r == 38);
    }

    function parenthesizedRightOperand() public pure {
        uint x = 10;
        uint y = 5;
        uint z = 3;
        uint r = x - (y - z);
        assert(r == 8);
    }

    function parenthesizedLeftOperand() public pure {
        uint x = 2;
        uint y = 3;
        uint z = 4;
        uint r = (x + y) * z;
        assert(r == 20);
    }

    function parenthesizedCondition() public pure {
        bool p = true;
        bool b = false;
        bool c = true;
        bool r = p && (b || c);
        assert(r);
    }

    function memoryFieldSubAssignUnfold() public pure {
        Person memory carol;
        carol.account.balance = 20;
        carol.account.balance -= 4;
        uint r = carol.account.balance;
        assert(r == 16);
    }

    function memoryFieldMulAssignUnfold() public pure {
        Person memory carol;
        carol.account.balance = 7;
        carol.account.balance *= 6;
        uint r = carol.account.balance;
        assert(r == 42);
    }

    function memoryFieldDivAssignUnfold() public pure {
        Person memory carol;
        carol.account.balance = 40;
        carol.account.balance /= 8;
        uint r = carol.account.balance;
        assert(r == 5);
    }

    function memoryFieldModAssignUnfold() public pure {
        Person memory carol;
        carol.account.balance = 40;
        carol.account.balance %= 7;
        uint r = carol.account.balance;
        assert(r == 5);
    }

    function memoryFieldPostincrementUnfold() public pure {
        Person memory carol;
        carol.account.balance = 20;
        carol.account.balance++;
        uint r = carol.account.balance;
        assert(r == 21);
    }

    function memoryFieldPredecrementUnfold() public pure {
        Person memory carol;
        carol.account.balance = 20;
        --carol.account.balance;
        uint r = carol.account.balance;
        assert(r == 19);
    }

    function memoryFieldPostdecrementUnfold() public pure {
        Person memory carol;
        carol.account.balance = 20;
        carol.account.balance--;
        uint r = carol.account.balance;
        assert(r == 19);
    }

    function memoryFieldDeleteUnfold() public pure {
        Person memory carol;
        carol.account.balance = 20;
        delete carol.account.balance;
        uint r = carol.account.balance;
        assert(r == 0);
    }

    function memoryFieldReadUnfoldResult() public pure {
        Person memory carol;
        Person memory david;
        david.age = 40;
        carol.account.balance = david.age;
        uint r = carol.account.balance;
        assert(r == 40);
    }

    function memoryIndexReadUnfoldResult() public pure {
        Person memory carol;
        uint[] memory xs = new uint[](2);
        xs[1] = 40;
        carol.account.balance = xs[1];
        uint r = carol.account.balance;
        assert(r == 40);
    }

    function memoryIndexArraySubAssignUnfold() public pure {
        Basket memory basket;
        uint[] memory xs = new uint[](4);
        basket.items = xs;
        basket.items[1] = 40;
        basket.items[1] -= 2;
        uint r = basket.items[1];
        assert(r == 38);
    }

    function memoryIndexArrayMulAssignUnfold() public pure {
        Basket memory basket;
        uint[] memory xs = new uint[](4);
        basket.items = xs;
        basket.items[1] = 7;
        basket.items[1] *= 6;
        uint r = basket.items[1];
        assert(r == 42);
    }

    function memoryIndexArrayDivAssignUnfold() public pure {
        Basket memory basket;
        uint[] memory xs = new uint[](4);
        basket.items = xs;
        basket.items[1] = 40;
        basket.items[1] /= 8;
        uint r = basket.items[1];
        assert(r == 5);
    }

    function memoryIndexArrayModAssignUnfold() public pure {
        Basket memory basket;
        uint[] memory xs = new uint[](4);
        basket.items = xs;
        basket.items[1] = 40;
        basket.items[1] %= 7;
        uint r = basket.items[1];
        assert(r == 5);
    }

    function memoryIndexArrayPostincrementUnfold() public pure {
        Basket memory basket;
        uint[] memory xs = new uint[](4);
        basket.items = xs;
        basket.items[1] = 40;
        basket.items[1]++;
        uint r = basket.items[1];
        assert(r == 41);
    }

    function memoryIndexArrayPredecrementUnfold() public pure {
        Basket memory basket;
        uint[] memory xs = new uint[](4);
        basket.items = xs;
        basket.items[1] = 40;
        --basket.items[1];
        uint r = basket.items[1];
        assert(r == 39);
    }

    function memoryIndexArrayPostdecrementUnfold() public pure {
        Basket memory basket;
        uint[] memory xs = new uint[](4);
        basket.items = xs;
        basket.items[1] = 40;
        basket.items[1]--;
        uint r = basket.items[1];
        assert(r == 39);
    }

    function memoryIndexArrayDeleteUnfold() public pure {
        Basket memory basket;
        uint[] memory xs = new uint[](4);
        basket.items = xs;
        basket.items[1] = 40;
        delete basket.items[1];
        uint r = basket.items[1];
        assert(r == 0);
    }

    function memoryIndexArrayPostincrement() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        xs[1]++;
        uint r = xs[1];
        assert(r == 41);
    }

    function memoryIndexArrayPredecrement() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        --xs[1];
        uint r = xs[1];
        assert(r == 39);
    }

    function memoryIndexArrayPreincrementAssignment() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        uint r = ++xs[1];
        assert(r == 41);
        assert(xs[1] == 41);
    }

    function memoryIndexArrayPostdecrementAssignment() public pure {
        uint[] memory xs = new uint[](4);
        xs[1] = 40;
        uint r = xs[1]--;
        assert(r == 40);
        assert(xs[1] == 39);
    }

    function storageFieldDeleteUnfold() public {
        alice.account.balance = 20;
        delete alice.account.balance;
        uint r = alice.account.balance;
        assert(r == 0);
    }

    function storageFieldPredecrementUnfold() public {
        alice.account.balance = 20;
        --alice.account.balance;
        uint r = alice.account.balance;
        assert(r == 19);
    }

    function storageFieldPostdecrementUnfold() public {
        alice.account.balance = 20;
        alice.account.balance--;
        uint r = alice.account.balance;
        assert(r == 19);
    }

    function storageIndexAddAssignUnfold() public {
        ledger.balances[1] = 40;
        ledger.balances[1] += 2;
        uint r = ledger.balances[1];
        assert(r == 42);
    }

    function storageIndexSubAssignUnfold() public {
        ledger.balances[1] = 40;
        ledger.balances[1] -= 2;
        uint r = ledger.balances[1];
        assert(r == 38);
    }

    function storageIndexMulAssignUnfold() public {
        ledger.balances[1] = 7;
        ledger.balances[1] *= 6;
        uint r = ledger.balances[1];
        assert(r == 42);
    }

    function storageIndexDivAssignUnfold() public {
        ledger.balances[1] = 40;
        ledger.balances[1] /= 8;
        uint r = ledger.balances[1];
        assert(r == 5);
    }

    function storageIndexModAssignUnfold() public {
        ledger.balances[1] = 40;
        ledger.balances[1] %= 7;
        uint r = ledger.balances[1];
        assert(r == 5);
    }

    function storageIndexPreincrementUnfold() public {
        ledger.balances[1] = 40;
        ++ledger.balances[1];
        uint r = ledger.balances[1];
        assert(r == 41);
    }

    function storageIndexPostincrementUnfold() public {
        ledger.balances[1] = 40;
        ledger.balances[1]++;
        uint r = ledger.balances[1];
        assert(r == 41);
    }

    function storageIndexPredecrementUnfold() public {
        ledger.balances[1] = 40;
        --ledger.balances[1];
        uint r = ledger.balances[1];
        assert(r == 39);
    }

    function storageIndexPostdecrementUnfold() public {
        ledger.balances[1] = 40;
        ledger.balances[1]--;
        uint r = ledger.balances[1];
        assert(r == 39);
    }

    function storageIndexMappingSubAssign() public {
        balances[1] = 40;
        balances[1] -= 2;
        uint r = balances[1];
        assert(r == 38);
    }

    function storageIndexMappingMulAssign() public {
        balances[1] = 7;
        balances[1] *= 6;
        uint r = balances[1];
        assert(r == 42);
    }

    function storageIndexMappingDivAssign() public {
        balances[1] = 40;
        balances[1] /= 8;
        uint r = balances[1];
        assert(r == 5);
    }

    function storageIndexMappingModAssign() public {
        balances[1] = 40;
        balances[1] %= 7;
        uint r = balances[1];
        assert(r == 5);
    }

    function storageIndexMappingPreincrement() public {
        balances[1] = 40;
        ++balances[1];
        uint r = balances[1];
        assert(r == 41);
    }

    function storageIndexMappingPostincrement() public {
        balances[1] = 40;
        balances[1]++;
        uint r = balances[1];
        assert(r == 41);
    }

    function storageIndexMappingPredecrement() public {
        balances[1] = 40;
        --balances[1];
        uint r = balances[1];
        assert(r == 39);
    }

    function storageIndexMappingPostdecrement() public {
        balances[1] = 40;
        balances[1]--;
        uint r = balances[1];
        assert(r == 39);
    }

    function storageIndexMappingPreincrementAssignment() public {
        balances[1] = 40;
        uint r = ++balances[1];
        assert(r == 41);
        assert(balances[1] == 41);
    }

    function storageIndexMappingPostincrementAssignment() public {
        balances[1] = 40;
        uint r = balances[1]++;
        assert(r == 40);
        assert(balances[1] == 41);
    }

    function storageIndexMappingPredecrementAssignment() public {
        balances[1] = 40;
        uint r = --balances[1];
        assert(r == 39);
        assert(balances[1] == 39);
    }

    function storageIndexMappingPostdecrementAssignment() public {
        balances[1] = 40;
        uint r = balances[1]--;
        assert(r == 40);
        assert(balances[1] == 39);
    }

    /// @custom:key box
    function storageIndexReadArrayStoreRoot() public {
        require(1 < values.length);
        values[1] = 40;
        age = values[1];
        uint r = age;
        assert(r == 40);
    }

    /// @custom:key box
    function storagePopUnfold() public {
        require(0 < basketA.items.length);
        basketA.items.pop();
    }

    function storageRootPostdecrement() public {
        age = 10;
        age--;
        uint r = age;
        assert(r == 9);
    }

    function storageRootPredecrementAssign() public {
        age = 10;
        uint r = --age;
        assert(r == 9);
        assert(age == 9);
    }

    function ternaryToIfStorage() public {
        bool b = true;
        age = b ? 1 : 2;
        uint r = age;
        assert(r == 1);
    }

    /// @custom:key box
    function transferToOwner() public {
        address payable to = payable(owner);
        to.transfer(5);
    }

    /// @custom:key box
    function transferUnfoldReceiver() public {
        payable(owner).transfer(5);
    }

    /// @custom:key box
    function transferUnfoldArgument() public {
        address payable to = payable(owner);
        uint x = 3;
        to.transfer(x + 2);
    }

    /// @custom:key box
    function sendToOwner() public {
        address payable to = payable(owner);
        bool ok = to.send(5);
        flag = ok;
    }

    /// @custom:key box
    function sendUnfoldReceiver() public {
        bool ok = payable(owner).send(5);
        flag = ok;
    }

    /// @custom:key box
    function sendUnfoldArgument() public {
        address payable to = payable(owner);
        uint x = 3;
        bool ok = to.send(x + 2);
        flag = ok;
    }

    /// @custom:key box
    function callToSender() public {
        uint amount = 5;
        (bool success, ) = payable(msg.sender).call{value: amount}("");
        flag = success;
    }

    /// @custom:key skip
    function tryCalleeGet(uint x) external pure returns (uint) {
        return x;
    }

    /// @custom:key skip
    function tryCalleePing() external pure {
    }

    /// @custom:key box
    function tryCallCatchKeepsState() public {
        total = 1;
        try TestSuite(owner).tryCalleePing() {
            total = 2;
        } catch {
            assert(total == 1);
        }
        assert(total == 1 || total == 2);
    }

    /// @custom:key box
    function tryCallBindsReturnAndPanicCode() public view {
        uint r = 0;
        try TestSuite(owner).tryCalleeGet(5) returns (uint v) {
            r = v + 1;
            assert(r == v + 1);
        } catch Error(string memory) {
            r = 2;
            assert(r == 2);
        } catch Panic(uint code) {
            r = code + 3;
            assert(r == code + 3);
        }
    }

    /// @custom:key box
    function tryCallUnmatchedFailureReverts() public {
        total = 3;
        try TestSuite(owner).tryCalleePing() {
            total = 4;
        } catch Error(string memory) {
            total = 5;
        }
        assert(total == 4 || total == 5);
    }

    // ── Internal calls, return statements and tuples ──

    function returnOne() internal pure returns (uint) {
        return 1;
    }

    function returnSign(int v) internal pure returns (int) {
        if (v < 0) return -1;
        if (v == 0) return 0;
        return 1;
    }

    function returnOrdered(uint x, uint y) internal pure returns (uint lo, uint hi) {
        if (x < y) return (x, y);
        return (y, x);
    }

    function returnSwapped() internal pure returns (uint x, uint y) {
        x = 1;
        y = 2;
        return (y, x);
    }

    function returnStats(uint x, uint y, uint z)
        internal pure returns (uint lo, uint hi, uint sum, bool same)
    {
        lo = x < y ? x : y;
        lo = lo < z ? lo : z;
        hi = x > y ? x : y;
        hi = hi > z ? hi : z;
        return (lo, hi, x + y + z, x == y && y == z);
    }

    function internalCallDeclaration() public pure {
        uint r = returnOne();
        assert(r == 1);
    }

    function internalCallInExpression() public pure {
        uint r = returnOne() + returnOne();
        assert(r == 2);
    }

    function internalCallToStorage() public {
        total = returnOne();
        assert(total == 1);
    }

    function returnEarly() public pure {
        int negative = returnSign(-3);
        int zero = returnSign(0);
        int positive = returnSign(4);
        assert(negative < 0 && zero == 0 && positive > 0);
    }

    function tupleReturnPair() public pure {
        (uint lo, uint hi) = returnOrdered(5, 2);
        assert(lo == 2 && hi == 5);
    }

    function tupleReturnReadsReturnVariables() public pure {
        (uint x, uint y) = returnSwapped();
        assert(x == 2 && y == 1);
    }

    function tupleReturnDiscardsComponents() public pure {
        (uint lo, , uint sum, bool same) = returnStats(3, 1, 2);
        assert(lo == 1 && sum == 6 && !same);
    }

    function tupleReturnAssignsExisting() public {
        uint hi;
        (total, hi) = returnOrdered(9, 4);
        assert(total == 4 && hi == 9);
    }

    function tupleAssignmentRotates() public pure {
        uint first = 1;
        uint second = 2;
        uint third = 3;
        (first, second, third) = (second, third, first);
        assert(first == 2 && second == 3 && third == 1);
    }

    function tupleDeclaration() public pure {
        (uint first, , bool third) = (4, 5, true);
        assert(first == 4 && third);
    }

    function returnFromNestedBlock(uint x) internal pure returns (uint) {
        {
            {
                if (x > 0) {
                    return 1;
                }
            }
            x = 5;
        }
        return x;
    }

    function returnOrFallThrough(bool stop) internal pure returns (uint r) {
        r = 5;
        if (stop) return r;
        r = 6;
    }

    function returnAddOne(uint x) internal pure returns (uint) {
        return x + 1;
    }

    function returnAddTwo(uint x) internal pure returns (uint) {
        uint y = returnAddOne(x);
        return returnAddOne(y);
    }

    function returnRevertsOnZero(uint x) internal pure returns (uint) {
        if (x == 0) revert();
        return x;
    }

    function returnInsideTry() internal view returns (uint) {
        try TestSuite(owner).tryCalleeGet(5) returns (uint) {
            return 7;
        } catch {
            return 8;
        }
    }

    function returnVoidEarly(uint v) internal {
        if (total != 0) return;
        total = v;
    }

    function returnLeavesNestedBlocks() public pure {
        uint one = returnFromNestedBlock(3);
        uint five = returnFromNestedBlock(0);
        assert(one == 1 && five == 5);
    }

    function returnOrFallThroughNamed() public pure {
        uint stopped = returnOrFallThrough(true);
        uint finished = returnOrFallThrough(false);
        assert(stopped == 5 && finished == 6);
    }

    function returnFromNestedCall() public pure {
        uint r = returnAddTwo(1);
        assert(r == 3);
    }

    function returnAfterRevertGuard() public pure {
        uint r = returnRevertsOnZero(3);
        assert(r == 3);
    }

    /// @custom:key box
    function returnFromTryBranches() public view {
        uint r = returnInsideTry();
        assert(r == 7 || r == 8);
    }

    function returnFromVoidFunction() public {
        total = 4;
        returnVoidEarly(9);
        assert(total == 4);
        total = 0;
        returnVoidEarly(9);
        assert(total == 9);
    }

    function returnDefaults() internal pure returns (uint r, bool b) {
    }

    function returnDefaultsAreZero() public pure {
        (uint r, bool b) = returnDefaults();
        assert(r == 0 && !b);
    }

    function returnDefaultAddress() internal pure returns (address who) {
    }

    function returnDefaultEnum() internal pure returns (Phase p) {
    }

    function returnDefaultMemoryArray() internal pure returns (uint[] memory xs) {
    }

    function returnInThenBranch(bool b) internal pure returns (uint r, bool ok) {
        if (b) {
            return (5, true);
        } else {
        }
    }

    function returnInElseBranch(bool b) internal view returns (address who) {
        if (b) {
        } else {
            return owner;
        }
    }

    function returnEnumInOneBranch(bool b) internal pure returns (Phase p) {
        if (b) return Phase.Closed;
    }

    function returnAssignsOneOfTwo() internal pure returns (uint r, address who) {
        r = who == address(0) ? 3 : 4;
    }

    function returnReadsItsDefault() internal pure returns (uint r, bool wasZero) {
        wasZero = r == 0;
    }

    function returnDefaultAddressIsZero() public pure {
        address who = returnDefaultAddress();
        assert(who == address(0));
    }

    function returnDefaultEnumIsFirstMember() public pure {
        Phase p = returnDefaultEnum();
        assert(p == Phase.Open);
    }

    function returnDefaultMemoryArrayIsEmpty() public pure {
        uint[] memory xs = returnDefaultMemoryArray();
        assert(xs.length == 0);
    }

    function returnInThenBranchElseIsDefault() public pure {
        (uint r, bool ok) = returnInThenBranch(true);
        assert(r == 5 && ok);
        (r, ok) = returnInThenBranch(false);
        assert(r == 0 && !ok);
    }

    function returnInElseBranchThenIsDefault() public view {
        address returned = returnInElseBranch(false);
        address fellThrough = returnInElseBranch(true);
        assert(returned == owner);
        assert(fellThrough == address(0));
    }

    function returnDefaultIsFreshPerCall() public pure {
        (uint first, ) = returnInThenBranch(true);
        (uint second, bool ok) = returnInThenBranch(false);
        assert(first == 5 && second == 0 && !ok);
    }

    function returnEnumOtherBranchIsDefault() public pure {
        Phase closed = returnEnumInOneBranch(true);
        Phase open = returnEnumInOneBranch(false);
        assert(closed == Phase.Closed && open == Phase.Open);
    }

    function returnUnassignedComponentIsDefault() public pure {
        (uint r, address who) = returnAssignsOneOfTwo();
        assert(r == 3 && who == address(0));
    }

    function returnDefaultIsVisibleInBody() public pure {
        (uint r, bool wasZero) = returnReadsItsDefault();
        assert(r == 0 && wasZero);
    }

    function overloadPick(uint x) internal pure returns (uint) {
        return x + 1;
    }

    function overloadPick(bool b) internal pure returns (uint) {
        return b ? 10 : 20;
    }

    function overloadedInternalCall() public pure {
        uint n = overloadPick(1);
        uint t = overloadPick(true);
        assert(n == 2 && t == 10);
    }

    // ── Modifiers ──

    modifier nonZero(uint v) {
        require(v > 0);
        _;
    }

    modifier countAround() {
        total = total + 1;
        _;
        total = total + 10;
    }

    modifier doubleAfter() {
        _;
        total = total * 2;
    }

    modifier addThreeAfter() {
        _;
        total = total + 3;
    }

    modifier setsFive() {
        total = 5;
        _;
    }

    function modifierGuarded(uint v) internal pure nonZero(v) returns (uint) {
        return v;
    }

    function modifierAroundBody() internal countAround returns (uint r) {
        r = total;
        return r;
    }

    function modifierOrdered() internal doubleAfter addThreeAfter {
        total = 1;
    }

    function modifierArgument() public pure {
        uint r = modifierGuarded(3);
        assert(r == 3);
    }

    function modifierResumesAfterReturn() public {
        total = 0;
        uint r = modifierAroundBody();
        assert(r == 1 && total == 11);
    }

    function modifierFirstListedOutermost() public {
        modifierOrdered();
        assert(total == 8);
    }

    function modifierOnObligation() public setsFive {
        assert(total == 5);
    }

    // ── Loops: unwound by whileUnwind after LoopLowering ──

    function whileCountsUp() public pure {
        uint i = 0;
        while (i < 3) {
            i = i + 1;
        }
        assert(i == 3);
    }

    function whileBodyDeclaresLocal() public pure {
        uint i = 0;
        uint s = 0;
        while (i < 3) {
            uint t = i * 2;
            s = s + t;
            i = i + 1;
        }
        assert(s == 6);
    }

    function whileBreakLeavesLoop() public pure {
        uint i = 0;
        while (i < 10) {
            if (i == 4) break;
            i = i + 1;
        }
        assert(i == 4);
    }

    function whileContinueSkipsRest() public pure {
        uint i = 0;
        uint s = 0;
        while (i < 5) {
            i = i + 1;
            if (i == 2) continue;
            s = s + i;
        }
        assert(s == 13);
    }

    function forContinueStillUpdates() public pure {
        uint s = 0;
        for (uint i = 0; i < 5; i++) {
            if (i == 1) {
                continue;
            }
            s = s + i;
        }
        assert(s == 9);
    }

    function forBreakKeepsCounter() public pure {
        uint i;
        for (i = 0; i < 9; i++) {
            if (i == 3) break;
        }
        assert(i == 3);
    }

    function doWhileRunsBodyFirst() public pure {
        uint i = 7;
        do {
            i = i + 1;
        } while (i < 3);
        assert(i == 8);
    }

    /// @custom:key box
    function forWritesStorageArray() public {
        require(values.length == 3);
        for (uint i = 0; i < values.length; i++) {
            values[i] = i * i;
        }
        assert(values[2] == 4);
    }

    function loopNestedReturn(uint k) internal pure returns (uint r) {
        for (uint i = 0; i < 3; i++) {
            for (uint j = 0; j < 3; j++) {
                if (i * 3 + j == k) {
                    return i * 10 + j;
                }
            }
        }
        r = 99;
    }

    function returnLeavesNestedLoops() public pure {
        uint r = loopNestedReturn(5);
        assert(r == 12);
        r = loopNestedReturn(20);
        assert(r == 99);
    }

    // ── Loop invariants: whileInvariantBox / whileInvariantDiamond ──

    /// @custom:key box
    function invariantCountsToBound(uint n) public pure {
        require(n >= 0);
        uint i = 0;
        /// @custom:key invariant i <= n
        while (i < n) {
            i = i + 1;
        }
        assert(i == n);
    }

    function invariantForCountsArrayLength() public view {
        uint c = 0;
        /// @custom:key invariant 0 <= i && i <= values.length && c == i
        /// @custom:key decreases values.length - i
        for (uint i = 0; i < values.length; i++) {
            c = c + 1;
        }
        assert(c == values.length);
    }

    function invariantClosedFormSum() public view {
        uint s = 0;
        uint i = 0;
        /// @custom:key invariant 0 <= i && i <= values.length && s == 2 * i
        /// @custom:key decreases values.length - i
        while (i < values.length) {
            s = s + 2;
            i = i + 1;
        }
        assert(s == 2 * values.length);
    }

    function invariantVariantSkipsBreakIteration(uint n) public pure {
        uint i = 0;
        /// @custom:key invariant 0 <= i && i <= 10
        /// @custom:key decreases 10 - i
        while (i < 10) {
            if (i == n) break;
            i = i + 1;
        }
        assert(i <= 10);
    }

    /// @custom:key box
    function invariantOverStorageWrites(uint n) public {
        require(n >= 0);
        total = 0;
        /// @custom:key invariant total == i && i <= n
        for (uint i = 0; i < n; i++) {
            total = total + 1;
        }
        assert(total == n);
    }

    /// @custom:key box
    function invariantQuantifiedOverPrefix() public {
        /// @custom:key invariant 0 <= i && i <= values.length
        /// @custom:key invariant \forall uint q; 0 <= q && q < i -> values[q] == 0
        for (uint i = 0; i < values.length; i++) {
            values[i] = 0;
        }
        assert(values.length == 0 || values[0] == 0);
    }

    // ── Constants, file-level declarations and libraries ──

    function constantInlined() public pure {
        uint r = LIMIT;
        assert(r == 7);
    }

    function contractQualifiedConstantAndEnum() public pure {
        uint r = TestSuite.LIMIT;
        TestSuite.Phase p = TestSuite.Phase.Closed;
        assert(r == 7);
        assert(p == Phase.Closed);
    }

    function fileLevelConstantEnumAndFunction() public pure {
        uint r = fileLevelTwice(FILE_LEVEL_LIMIT);
        FileLevelColor c = FileLevelColor.Blue;
        assert(r == 84);
        assert(uint(c) == 2);
    }

    function fileLevelStructThroughLibrary() public {
        pair.left = 1;
        pair.right = 2;
        PairLib.swap(pair);
        uint l = pair.left;
        assert(l == 2);
    }

    function libraryCallAndUsingFor() public pure {
        uint v = 5;
        assert(PairLib.bump(v) == 15);
        assert(v.bump() == 15);
        assert(PairLib.UNIT == 10);
    }

    function valueTypeWrapUnwrap() public pure {
        Wei w = Wei.wrap(3);
        assert(Wei.unwrap(w) == 3);
    }

    function typeBounds() public pure {
        uint8 m = type(uint8).max;
        int8 n = type(int8).min;
        int e = -128;
        assert(m == 255);
        assert(n == e);
        assert(uint(type(FileLevelColor).max) == 2);
    }

    function addmodMulmod() public pure {
        assert(addmod(10, 5, 7) == 1);
        assert(mulmod(3, 5, 7) == 1);
    }

    // ── Parameters and modifiers ──

    function setTotalToOne() internal {
        total = 1;
    }

    modifier callsInternal() {
        setTotalToOne();
        _;
    }

    function modifierCallsInternalFunction() public callsInternal {
        assert(total == 1);
    }

    function firstOf(uint[] memory xs) internal pure returns (uint) {
        return xs[0];
    }

    function indexParameter() public pure {
        uint[] memory xs = new uint[](1);
        xs[0] = 9;
        uint r = firstOf(xs);
        assert(r == 9);
    }

    function setTokenValue(Token storage t, uint v) internal {
        t.value = v;
    }

    function readTokenValue(Token storage t) internal view returns (uint) {
        return t.value;
    }

    function storageStructParameter() public {
        setTokenValue(tok, 4);
        uint r = readTokenValue(tok);
        assert(r == 4);
    }

    function credit(mapping(uint => uint) storage m, uint k) internal {
        m[k] = 1;
    }

    function storageMappingParameter() public {
        credit(valuesMap, 3);
        uint r = valuesMap[3];
        assert(r == 1);
    }

    /// @custom:key box
    function pinWithInequality(uint x, uint y) public pure {
        require(y != 0 && x == 42);
        assert(x == 42);
    }

    /// @custom:key box
    function payableAddressParameter(address payable p) public pure {
        require(p == 0x5B38Da6a701c568545dCfcB03FcB875f56beddC4);
        assert(p != address(0));
    }

    function digits(uint p, uint q, uint s) internal pure returns (uint r) {
        r = p * 100 + q * 10 + s;
    }

    function namedArgumentsBindByName() public pure {
        uint r = digits({q: 2, s: 3, p: 1});
        assert(r == 123);
    }

    modifier keepsLocal(uint y) {
        uint c = y;
        _;
        localOut = c;
    }

    function twiceKeepsLocal() internal keepsLocal(2) keepsLocal(5) {}

    function modifierLocalsArePerApplication() public {
        twiceKeepsLocal();
        uint r = localOut;
        assert(r == 2);
    }

    function uninitialisedLocalsAreDefault() public pure {
        uint x;
        bool b;
        address addr;
        assert(x == 0);
        assert(!b);
        assert(addr == address(0));
    }

    function storageStaticToDynamicCopyKeepsLength() public {
        copySource9[8] = 4;
        copyTargetDyn = copySource9;
        uint n = copyTargetDyn.length;
        uint r = copyTargetDyn[8];
        assert(n == 9);
        assert(r == 4);
    }

    function storageShorterStaticCopyClearsTail() public {
        copyBig[30] = 4;
        copySmall[3] = 8;
        copyBig = copySmall;
        uint head = copyBig[3];
        uint tail = copyBig[30];
        assert(head == 8);
        assert(tail == 0);
    }

    function testFixedArrayOfFixedArraysLength() public view {
        assert(fixedGrid.length == 2);
        assert(fixedGrid[1].length == 3);
    }

    function testEmptyPushReadsDefaultValue() public {
        uint n = values.length;
        values.push();
        assert(values.length == n + 1);
        assert(values[n] == 0);
    }

    function testPopPushValueResetsValue() public {
        uint n = values.length;
        values.push(73);
        values.pop();
        assert(values.length == n);
        values.push();
        assert(values.length == n + 1);
        assert(values[n] == 0);
    }

    function testFixedCopyThenEmptyPushReadsZero() public {
        copySource9[8] = 41;
        copyTargetDyn = copySource9;
        copySource9[8] = 42;
        copyTargetDyn.push();
        assert(copySource9.length == 9);
        assert(copyTargetDyn.length == 10);
        assert(copyTargetDyn[8] == 41);
        assert(copyTargetDyn[9] == 0);
    }

    function testShorterCopyThenEmptyPushClearsTail() public {
        copyTargetDyn = copySource9;
        copyTargetDyn.push(99);
        copyTargetDyn = copySource9;
        assert(copyTargetDyn.length == 9);
        copyTargetDyn.push();
        assert(copyTargetDyn[9] == 0);
    }

    function testPushMappingOfFixedArrayPreservesEntries() public {
        delete dynMapsOfFixed;
        dynMapsOfFixed.push();
        dynMapsOfFixed[0][7][2] = 19;
        dynMapsOfFixed.pop();
        dynMapsOfFixed.push();
        assert(dynMapsOfFixed.length == 1);
        assert(dynMapsOfFixed[0][7].length == 3);
        assert(dynMapsOfFixed[0][7][2] == 19);
    }

    function testShapeCopyFixedTailAndSourceIndependence() public {
        copySmall[0] = 11;
        copySmall[19] = 12;
        copyBig[20] = 93;
        copyBig[39] = 94;
        copyBig = copySmall;
        assert(copySmall.length == 20);
        assert(copyBig.length == 40);
        assert(copyBig[0] == 11);
        assert(copyBig[19] == 12);
        assert(copyBig[20] == 0);
        assert(copyBig[39] == 0);
        copySmall[0] = 99;
        assert(copyBig[0] == 11);
    }

    function testShapeCopyDynamicShrinkClearsReusedSlot() public {
        delete a;
        delete values;
        a.push(11);
        a.push(12);
        values.push(91);
        values.push(92);
        values.push(93);
        values = a;
        assert(values.length == 2);
        assert(values[0] == 11);
        assert(values[1] == 12);
        values.push();
        assert(values[2] == 0);
        values[0] = 99;
        assert(a[0] == 11);
    }

    function testShapeCopyNestedSelfAliasPreservesValues() public {
        fixedGrid[0][2] = 11;
        fixedGrid[1][2] = 12;
        uint[3][2] storage same = fixedGrid;
        fixedGrid = same;
        assert(fixedGrid.length == 2);
        assert(fixedGrid[0].length == 3);
        assert(fixedGrid[0][2] == 11);
        assert(fixedGrid[1][2] == 12);
    }

    function testFixedArrayOfMappingsOfFixedArraysLength() public view {
        assert(fixedMapsOfFixed[1][7].length == 3);
    }

    /// @custom:key box
    function testDynamicArrayOfMappingsOfFixedArraysLength() public view {
        require(0 < dynMapsOfFixed.length);
        assert(dynMapsOfFixed[0][7].length == 3);
    }

    function testPushIndexedPrimitiveSourceOnce() public {
        delete values;
        values.push(11);
        uint i = 0;
        values.push(values[i++]);
        assert(i == 1);
        assert(values.length == 2);
        assert(values[0] == 11);
        assert(values[1] == 11);
    }

    function testPushIndexedFixedArraySourceOnce() public {
        delete rows;
        rows.push();
        rows[0][0] = 11;
        uint i = 0;
        rows.push(rows[i++]);
        assert(i == 1);
        assert(rows.length == 2);
        rows[0][0] = 99;
        assert(rows[1].length == 3);
        assert(rows[1][0] == 11);
    }

    function testFixedShapePopPushResetsFixedElement() public {
        uint n = rows.length;
        rows.push();
        rows[n][0] = 11;
        rows[n][2] = 22;
        rows.pop();
        assert(rows.length == n);
        rows.push();
        assert(rows[n].length == 3);
        assert(rows[n][0] == 0);
        assert(rows[n][2] == 0);
    }

    function testFixedShapeDeleteFixedElementKeepsLength() public {
        uint n = rows.length;
        rows.push();
        rows[n][1] = 17;
        delete rows[n];
        assert(rows.length == n + 1);
        assert(rows[n].length == 3);
        assert(rows[n][1] == 0);
    }

    function testFixedShapeDeleteDynamicThenPushFixedElement() public {
        rows.push();
        rows[0][2] = 23;
        delete rows;
        assert(rows.length == 0);
        rows.push();
        assert(rows.length == 1);
        assert(rows[0].length == 3);
        assert(rows[0][2] == 0);
    }

    function testFixedShapeFixedElementStorageAlias() public {
        uint n = rows.length;
        rows.push();
        uint[3] storage row = rows[n];
        assert(row.length == 3);
        row[2] = 31;
        assert(rows[n][2] == 31);
        delete rows[n];
        assert(row.length == 3);
        assert(row[2] == 0);
    }

    function testFixedShapeEmptyPushFixedElementReadsZero() public {
        uint n = rows.length;
        rows.push();
        assert(rows.length == n + 1);
        assert(rows[n].length == 3);
        assert(rows[n][0] == 0);
        assert(rows[n][2] == 0);
    }

    function testEmptyPushFixedArrayReturnReadsZero() public {
        uint[3] storage row = rows.push();
        assert(row.length == 3);
        assert(row[0] == 0);
        assert(row[2] == 0);
    }

    function testEmptyPushDynamicArrayReturnReadsZero() public {
        uint[] storage row = matrix.push();
        assert(row.length == 0);
        row.push();
        assert(row[0] == 0);
    }

    function testEmptyPushStructReturnReadsZero() public {
        Token storage token = tokens.push();
        assert(token.value == 0);
    }
}
