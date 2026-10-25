import SolidityVelvet.Contract

/-!
# solkey's test suite in Velvet

One contract that exercises the Solidity notation of
`Bridge/SolidityVelvet/Contract.lean` feature by feature, every function
proved by Velvet (`prove_contract TestSuite by loom_solve`, at the end).
The functions are solkey's own
(`tests/migration/solkey/keyext.solidity.examples/TestSuite.sol`), under
their names there: each sets up storage or locals, runs the feature, and
states what holds after it with `assert`, which here is a proof obligation.
solkey's `/// @custom:key invariant` comments are `invariant` clauses, and
its loops that KeY unwinds have one too, since Velvet does not unwind.

Kept are the tests whose features the notation has: `uint` and `bool`
storage roots, mappings (nested, and keyed by `bool`), arrays (nested, with
`push`, `pop` and `.length`), arithmetic with its reverts, comparisons and
the logical operators, the ternary, `require`, `assert`, `delete`,
compound assignments, increments and decrements, `if`/`else`, `while` and
`for`. Where solkey writes a field (`alice.age`), the test here writes a
storage root (`age`); the tests that need structs, storage aliases, memory,
internal or external calls, `break`, `continue` or effects inside
expressions (`uint r = age++`) are left out. A decrement is `x−−` (two
U+2212), as in the core's `sol{ … }`, since `--` opens a Lean comment.
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

contract TestSuite {
  uint age;
  uint balance;
  uint total;
  bool flag;
  uint[] values;
  uint[][] matrix;
  mapping(uint => uint) balances;
  mapping(uint => bool) flags;
  mapping(uint => uint) valuesMap;
  mapping(uint => mapping(uint => uint)) grid;
  mapping(bool => uint) boolKeyed;

  -- Arithmetic

  function additionStorageWrite(uint x, uint y) public {
    require(x == 5 && y == 7);
    age = x + y;
    uint r = age;
    assert(r == 12);
  }

  function additionSimple() public pure {
    uint r = 1 + 2;
    assert(r == 3);
  }

  function additionStorageRead() public {
    age = 10;
    uint r = age + 1;
    assert(r == 11);
  }

  function subtractionSimple() public pure {
    uint r = 7 - 2;
    assert(r == 5);
  }

  function subtractionStorageRead() public {
    age = 10;
    uint r = age - 3;
    assert(r == 7);
  }

  function multiplicationSimple() public pure {
    uint r = 3 * 4;
    assert(r == 12);
  }

  function divisionSimple() public pure {
    uint r = 8 / 2;
    assert(r == 4);
  }

  function moduloSimple() public pure {
    uint r = 7 % 3;
    assert(r == 1);
  }

  function powerSimple() public pure {
    uint r = 2 ** 3;
    assert(r == 8);
  }

  function localArithmeticInRange(uint x) public pure {
    require(x >= 1 && x <= 100);
    uint r;
    r = x + 1;
    r -= 1;
    ++r;
    assert(r == x + 1);
  }

  -- Comparison and logic

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

  function notEqualSimple() public pure {
    bool r = 3 != 4;
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

  -- Conditionals

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

  -- Require and assert

  function requireTrueLiteral() public pure {
    require(true);
    assert(true);
  }

  function requireFalseLiteral() public pure {
    require(false);
    assert(false);
  }

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

  function testSimpleAssert() public {
    age = 42;
    uint v = age;
    assert(v == 42);
  }

  -- Storage: root

  function storageRootReadWrite() public {
    age = 34;
    uint r = age;
    assert(r == 34);
  }

  function storageRootAddAssign() public {
    age = 10;
    age += 5;
    uint r = age;
    assert(r == 15);
  }

  function storageRootSubAssign() public {
    age = 10;
    age -= 4;
    uint r = age;
    assert(r == 6);
  }

  function storageRootMulAssign() public {
    age = 6;
    age *= 3;
    uint r = age;
    assert(r == 18);
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

  function storageRootMultipleWrites() public {
    age = 1;
    age = 2;
    uint r = age;
    assert(r == 2);
  }

  function storageRootPostincrement() public {
    age = 10;
    age++;
    uint r = age;
    assert(r == 11);
  }

  function storageRootPreincrement() public {
    age = 10;
    ++age;
    uint r = age;
    assert(r == 11);
  }

  function storageRootPredecrement() public {
    age = 10;
    −−age;
    uint r = age;
    assert(r == 9);
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

  function storageRootWriteRhsCapture(uint x, uint y, uint z) public {
    require(x == 1 && y == 2 && z == 3);
    total = x + y * z;
    uint r = total;
    assert(r == 7);
  }

  function storageBoolRootReadWrite() public {
    flag = true;
    bool r = flag;
    assert(r);
  }

  -- Storage: mappings

  function storageIndexRootMapping() public {
    balances[1] = 42;
    uint r = balances[1];
    assert(r == 42);
  }

  function storageIndexMappingAddAssign() public {
    balances[1] = 40;
    balances[1] += 2;
    uint r = balances[1];
    assert(r == 42);
  }

  function storageIndexReadMappingStoreRoot(uint k) public {
    require(k == 1);
    balances[1] = 42;
    total = balances[k];
    uint r = total;
    assert(r == 42);
  }

  function storageIndexWriteNseChain(uint i, uint x, uint y) public {
    require(i == 2 && x == 3 && y == 4);
    balances[i + 1] = x * y + 3;
    uint r = balances[3];
    assert(r == 15);
  }

  function storageIndexDeleteMappingBool() public {
    flags[1] = true;
    delete flags[1];
    bool r = flags[1];
    assert(!r);
  }

  function storageIndexDeleteNseIndex(uint k) public {
    require(k == 2);
    balances[3] = 7;
    delete balances[k + 1];
    uint r = balances[3];
    assert(r == 0);
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

  function storageIndexCopyValue(uint i, uint j) public {
    require(1 < values.length);
    require(i == 5 && j == 1);
    values[1] = 8;
    balances[i] = values[j];
    uint r = balances[5];
    assert(r == 8);
  }

  function storageGridWriteRead() public {
    grid[2][3] = 99;
    grid[3][2] = 1;
    uint r = grid[2][3];
    assert(r == 99);
  }

  function storageBoolKeyedMapping() public {
    boolKeyed[true] = 1;
    boolKeyed[false] = 2;
    assert(boolKeyed[true] == 1);
  }

  -- Storage: arrays

  function storageIndexAddAssign() public {
    require(1 < values.length);
    values[1] = 40;
    values[1] += 2;
    uint r = values[1];
    assert(r == 42);
  }

  function storageIndexSubAssign() public {
    require(1 < values.length);
    values[1] = 40;
    values[1] -= 8;
    uint r = values[1];
    assert(r == 32);
  }

  function storageIndexMultipleWrites() public {
    require(3 < values.length);
    values[3] = 5;
    values[3] = 8;
    uint r = values[3];
    assert(r == 8);
  }

  function storageIndexPostincrement() public {
    require(1 < values.length);
    values[1] = 40;
    values[1]++;
    uint r = values[1];
    assert(r == 41);
  }

  function storageIndexPostdecrement() public {
    require(1 < values.length);
    values[1] = 40;
    values[1]−−;
    uint r = values[1];
    assert(r == 39);
  }

  function storageIndexDelete() public {
    require(1 < values.length);
    values[1] = 7;
    delete values[1];
    uint r = values[1];
    assert(r == 0);
  }

  function storageIndexReadNseIndex(uint i) public {
    require(2 < values.length);
    require(i == 1);
    values[2] = 9;
    uint r = values[i + 1];
    assert(r == 9);
  }

  function storageIndexArrayAddAssignOutOfBoundsReverts() public {
    require(values.length == 0);
    values[1] += 2;
    assert(false);
  }

  function storageIndexArrayReadOutOfBoundsReverts() public view {
    require(values.length == 0);
    uint r = values[1];
    assert(r != r);
  }

  function storageMatrixWriteRead() public {
    require(2 < matrix.length);
    require(3 < matrix[2].length);
    matrix[2][3] = 99;
    uint r = matrix[2][3];
    assert(r == 99);
  }

  function storageMatrixNseIndex(uint i, uint j, uint x, uint y) public {
    require(2 < matrix.length);
    require(3 < matrix[2].length);
    require(i == 1 && j == 2 && x == 5 && y == 6);
    matrix[i + 1][j + 1] = x + y;
    assert(matrix[2][3] == 11);
  }

  -- Storage: push and pop

  function storagePushEmpty() public {
    require(values.length == 2);
    values.push();
    assert(values.length == 3);
  }

  function storagePushLengthPositive() public {
    values.push();
    assert(values.length > 0);
  }

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

  function storagePopAfterPush() public {
    require(values.length == 0);
    values.push();
    values.pop();
    assert(values.length == 0);
  }

  function storagePopNonempty() public {
    require(values.length == 2);
    values.pop();
    assert(values.length == 1);
    values.push();
    assert(values[1] == 0);
  }

  function storagePopUnknownLength() public {
    values.push();
    values.pop();
  }

  -- Loops

  function whileCountsUp() public pure {
    uint i = 0;
    while (i < 3)
      invariant i <= 3
    {
      i = i + 1;
    }
    assert(i == 3);
  }

  function whileBodyDeclaresLocal() public pure {
    uint i = 0;
    uint s = 0;
    while (i < 3)
      invariant (i == 0 && s == 0) || (i == 1 && s == 0)
        || (i == 2 && s == 2) || (i == 3 && s == 6)
    {
      uint t = i * 2;
      s = s + t;
      i = i + 1;
    }
    assert(s == 6);
  }

  function forWritesStorageArray() public {
    require(values.length == 3);
    for (uint i = 0; i < values.length; i++)
      invariant i <= values.length && values.length == 3
      invariant forall (uint j) j < i ==> values[j] == j * j
    {
      values[i] = i * i;
    }
    assert(values[2] == 4);
  }

  function invariantCountsToBound(uint n) public pure {
    require(n >= 0);
    uint i = 0;
    while (i < n)
      invariant i <= n
    {
      i = i + 1;
    }
    assert(i == n);
  }

  function invariantForCountsArrayLength() public view {
    uint c = 0;
    for (uint i = 0; i < values.length; i++)
      invariant 0 <= i && i <= values.length && c == i
    {
      c = c + 1;
    }
    assert(c == values.length);
  }
}

prove_contract TestSuite by
  loom_solve

/-! Each function also runs: its storage, then its arguments, and the storage
it wrote beside its result (`()` for none). -/

/-- info: DivM.res ((), 12) -/
#guard_msgs in
#eval (TestSuite.additionStorageWrite 0 5 7).run

/-- info: DivM.res ((), #[0, 1, 4]) -/
#guard_msgs in
#eval (TestSuite.forWritesStorageArray #[7, 7, 7]).run

/-- info: DivM.res ((), #[42]) -/
#guard_msgs in
#eval (TestSuite.storagePushReadBack #[]).run
