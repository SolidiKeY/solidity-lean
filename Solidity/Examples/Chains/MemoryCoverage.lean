import Solidity.Calculus.Chains
import Solidity.Calculus.Close

/-!
# Memory rule coverage: one step per rule

A table, one row per rule: a statement, and the line its rule gives, `φ ~[r]~> ψ`
(`Examples/ChainNotation.lean` says how to read one).  The rule's name is Lean's; where the printed
trace names it differently, the printed name follows in a comment.

A memory object is declared by a `where` clause, `Person memory carol`, as the printer writes it
(`Calculus/Notation.lean`); the row `Person memory carol;` declares it in the program.

Stand-ins: `carol.account.values` and `carol.account.tokens` are `basket.items` and
`bucket.tokens` (`Account` has neither member).  A statement holding a call (`makeValue()`)
is the elaborator's first step, an equation, not a rule; so is a `++` in an operand.
Rows are single links, not chains: the ends-merged convention and `#last_line` do not apply here.
-/

namespace Solidity.Examples.Chains.MemoryCoverage

/-- Memory needs no state; `makeValue()` is the call of its row. -/
def MemCoverage : Contract := contract!{
  uint total;
  function makeValue() returns (uint) { return total; }
}

local instance : InContract := ⟨MemCoverage⟩

/-! ### Field writes -/

example : dl!{ ⟨ carol.account.balance = balanceVal; ⟩ true where Person memory carol }
    ~[memoryFieldWrite_unfold_leftFst]~>
      dl!{ ⟨ Account memory mv1 = carol.account; mv1.balance = balanceVal; ⟩ true where Person memory carol } :=
  rfl

-- printed `memoryFieldWriteMemRef_unfold_leftFst`
example : dl!{ ⟨ carol.account.token = tok; ⟩ true where Person memory carol, Token memory tok }
    ~[memoryFieldWrite_unfold_leftFst]~>
      dl!{ ⟨ Account memory mv1 = carol.account; mv1.token = tok; ⟩ true
        where Person memory carol, Token memory tok } := rfl

-- printed `fieldWriteValueRhsCapture`
example : dl!{ ⟨ carol.age = ageVal + 1; ⟩ true where Person memory carol }
    ~[memoryFieldWriteUnfoldSource]~>
      dl!{ ⟨ uint se1 = ageVal + 1; carol.age = se1; ⟩ true where Person memory carol } := rfl

-- printed `memoryFieldWriteCaptureSrc`: a memory path is a source as it stands.
example : dl!{ ⟨ carol.account = david.account; ⟩ true where Person memory carol, Person memory david }
    ~[memoryFieldWriteCopy]~>
      dl!{ { memory := write(memory, carol.account, read(memory, david.account)) } ⟨⟩ true
        where Person memory carol, Person memory david } := rfl

-- printed `memoryFieldWrite`
example : dl!{ ⟨ carol.account = acc; ⟩ true where Person memory carol, Account memory acc }
    ~[memoryFieldWriteCopy]~>
      dl!{ { memory := write(memory, carol.account, acc) } ⟨⟩ true
        where Person memory carol, Account memory acc } := rfl

-- printed `memoryFieldWrite`
example : dl!{ ⟨ carol.age = ageVal; ⟩ true where Person memory carol }
    ~[memoryFieldWriteStore]~>
      dl!{ { memory := write(memory, carol.age, ageVal) } ⟨⟩ true where Person memory carol } := rfl

/-! ### Aliases, declarations and allocation -/

-- printed `memoryRootRebind`
example : dl!{ ⟨ carol = david; ⟩ true where Person memory carol, Person memory david }
    ~[memoryRootAlias]~>
      dl!{ { carol := david } ⟨⟩ true where Person memory carol, Person memory david } := rfl

example : dl!{ ⟨ Account memory acc = carol.account; ⟩ true where Person memory carol }
    ~[memoryLocalDeclInitDrop]~> dl!{ ⟨ acc = carol.account; ⟩ true where Person memory carol } := rfl

example : dl!{ ⟨ Person memory carol; ⟩ true }
    ~[memoryReferenceDeclFreshAlloc]~>
      dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨⟩ true } := rfl

example : dl!{ ⟨ xs = new uint[](n); ⟩ true where uint[] memory xs }
    ~[memoryArrayFreshAlloc]~>
      dl!{ { xs := freshId(copySt(memory, newArr(uint[], n))) ‖ memory := copySt(memory, newArr(uint[], n)) }
        ⟨⟩ true where uint[] memory xs } := rfl

-- `basket.items` for `carol.account.values`.
example : dl!{ ⟨ basket.items = new uint[](n); ⟩ true where Basket memory basket }
    ~[newArrayCapture]~>
      dl!{ ⟨ uint[] memory mv1 = new uint[](n); basket.items = mv1; ⟩ true where Basket memory basket } := rfl

/-! ### Field reads -/

example : dl!{ ⟨ v = carol.account.balance; ⟩ true where Person memory carol }
    ~[memoryFieldRead_unfold_rightFst]~>
      dl!{ ⟨ Account memory mv1 = carol.account; v = mv1.balance; ⟩ true where Person memory carol } := rfl

-- printed `memoryFieldRead`
example : dl!{ ⟨ carolAcc = david.account; ⟩ true
      where Person memory david, Account memory carolAcc }
    ~[memoryFieldReadAliasRoot]~>
      dl!{ { carolAcc := read(memory, david.account) } ⟨⟩ true
        where Person memory david, Account memory carolAcc } := rfl

-- printed `memoryFieldRead_unfold_rightSndResult`: the strategy unfolds the target first;
-- the source read of `carol.age = acc.balance;` is captured by the value-source rule.
example : dl!{ ⟨ carol.account.balance = acc.balance; ⟩ true where Person memory carol, Account memory acc }
    ~[memoryFieldWrite_unfold_leftFst]~>
      dl!{ ⟨ Account memory mv1 = carol.account; mv1.balance = acc.balance; ⟩ true
        where Person memory carol, Account memory acc } := rfl

example : dl!{ ⟨ carol.age = acc.balance; ⟩ true where Person memory carol, Account memory acc }
    ~[memoryFieldWriteUnfoldSource]~>
      dl!{ ⟨ uint se1 = acc.balance; carol.age = se1; ⟩ true where Person memory carol, Account memory acc } :=
  rfl

-- printed `memoryFieldRead`
example : dl!{ ⟨ v = carol.age; ⟩ true where Person memory carol }
    ~[memoryFieldReadHeap]~> dl!{ { v := read(memory, carol.age) } ⟨⟩ true where Person memory carol } := rfl

-- printed `memoryRootRebind`
example : dl!{ ⟨ carolAlias = carol; ⟩ true where Person memory carol, Person memory carolAlias }
    ~[memoryRootAlias]~>
      dl!{ { carolAlias := carol } ⟨⟩ true where Person memory carol, Person memory carolAlias } := rfl

/-! ### `delete` -/

example : dl!{ ⟨ delete carol; ⟩ true where Person memory carol }
    ~[memoryRootDeleteFreshRebind]~>
      dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨⟩ true
        where Person memory carol } := rfl

example : dl!{ ⟨ delete carol.age; ⟩ true where Person memory carol }
    ~[memoryFieldDeletePrimitive]~>
      dl!{ { memory := write(memory, carol.age, 0) } ⟨⟩ true where Person memory carol } := rfl

example : dl!{ ⟨ delete carol.account; ⟩ true where Person memory carol }
    ~[memoryFieldDeleteReference]~>
      dl!{ { memory := write(addM(memory, Account), carol.account, freshId(addM(memory, Account))) } ⟨⟩ true
        where Person memory carol } := rfl

example : dl!{ ⟨ delete carolValues[i]; ⟩ true where uint[] memory carolValues }
    ~[memoryIndexDeletePrimitive]~>
      dl!{ { memory := write(memory, carolValues[i], 0) } ⟨⟩ true where uint[] memory carolValues } := rfl

example : dl!{ ⟨ delete carolTokens[i]; ⟩ true where Token[] memory carolTokens }
    ~[memoryIndexDeleteReference]~>
      dl!{ { memory := write(addM(memory, Token), carolTokens[i], freshId(addM(memory, Token))) } ⟨⟩ true
        where Token[] memory carolTokens } := rfl

example : dl!{ ⟨ delete carol.account.token; ⟩ true where Person memory carol }
    ~[memoryFieldDelete_unfold_leftFst]~>
      dl!{ ⟨ Account memory mv1 = carol.account; delete mv1.token; ⟩ true where Person memory carol } := rfl

-- `bucket.tokens` for `carol.account.tokens`.
example : dl!{ ⟨ delete bucket.tokens[i]; ⟩ true where TokenBucket memory bucket }
    ~[memoryIndexDelete_unfold_leftFst]~>
      dl!{ ⟨ Token[] memory mv1 = bucket.tokens; delete mv1[i]; ⟩ true where TokenBucket memory bucket } := rfl

/-! ### Index writes -/

-- The receiver and the `++i` are captured by the elaborator; `basket.items` for
-- `carol.account.values`.
example : dl!{ ⟨ basket.items[++i] = val; ⟩ true where Basket memory basket }
    = dl!{ ⟨ uint se1 = val; uint[] memory mv2 = basket.items; uint se3; se3 = ++i; mv2[se3] = se1; ⟩ true
        where Basket memory basket } := rfl

-- `bucket.tokens` for `carol.account.tokens`.
example : dl!{ ⟨ bucket.tokens[i] = carolToken; ⟩ true where TokenBucket memory bucket, Token memory carolToken }
    ~[memoryIndexWriteMemRefCaptureAllComplexRecv]~>
      dl!{ ⟨ Token[] memory mv1 = bucket.tokens; uint ie1 = i; mv1[ie1] = carolToken; ⟩ true
        where TokenBucket memory bucket, Token memory carolToken } := rfl

example : dl!{ ⟨ carolValues[++i] = val; ⟩ true where uint[] memory carolValues }
    = dl!{ ⟨ uint se1 = val; uint se2; se2 = ++i; carolValues[se2] = se1; ⟩ true
        where uint[] memory carolValues } := rfl

example : dl!{ ⟨ carolTokens[++i] = carolToken; ⟩ true where Token[] memory carolTokens, Token memory carolToken }
    = dl!{ ⟨ uint se1; se1 = ++i; carolTokens[se1] = carolToken; ⟩ true
        where Token[] memory carolTokens, Token memory carolToken } := rfl

-- The call is the elaborator's.
example : dl!{ ⟨ carolValues[i] = makeValue(); ⟩ true where uint[] memory carolValues }
    = dl!{ ⟨ uint se1; se1 = makeValue(); carolValues[i] = se1; ⟩ true where uint[] memory carolValues } := rfl

-- printed `memoryIndexWriteMemRefRhsCapture`: the receiver `david.account` is unfolded first.
example : dl!{ ⟨ carolTokens[i] = david.account.token; ⟩ true where Token[] memory carolTokens, Person memory david }
    ~[memoryFieldRead_unfold_rightFst]~>
      dl!{ ⟨ Account memory mv1 = david.account; carolTokens[i] = mv1.token; ⟩ true
        where Token[] memory carolTokens, Person memory david } := rfl

-- printed `memoryIndexWriteArray`
example : dl!{ ⟨ carolTokens[i] = carolToken; ⟩ true where Token[] memory carolTokens, Token memory carolToken }
    ~[memoryIndexWriteCopy]~>
      dl!{ { memory := write(memory, carolTokens[i], carolToken) } ⟨⟩ true
        where Token[] memory carolTokens, Token memory carolToken } := rfl

-- printed `memoryIndexWriteArray`
example : dl!{ ⟨ carolValues[i] = val; ⟩ true where uint[] memory carolValues }
    ~[memoryIndexWriteStore]~>
      dl!{ { memory := write(memory, carolValues[i], val) } ⟨⟩ true where uint[] memory carolValues } := rfl

/-! ### Index reads -/

-- `basket.items` for `carol.account.values`.
example : dl!{ ⟨ v = basket.items[i]; ⟩ true where Basket memory basket }
    ~[memoryIndexRead_unfold_rightFst]~>
      dl!{ ⟨ uint[] memory mv1 = basket.items; v = mv1[i]; ⟩ true where Basket memory basket } := rfl

example : dl!{ ⟨ v = carolValues[++i]; ⟩ true where uint[] memory carolValues }
    = dl!{ ⟨ uint se1; se1 = ++i; v = carolValues[se1]; ⟩ true where uint[] memory carolValues } := rfl

-- printed `memoryIndexReadArrayMemory`
example : dl!{ ⟨ carolToken = davidTokens[i]; ⟩ true where Token[] memory davidTokens, Token memory carolToken }
    ~[memoryIndexReadAliasRoot]~>
      dl!{ { carolToken := read(memory, davidTokens[i]) } ⟨⟩ true
        where Token[] memory davidTokens, Token memory carolToken } := rfl

-- printed `memoryIndexRead_unfold_rightSndResult`
example : dl!{ ⟨ carol.age = carolValues[i]; ⟩ true where Person memory carol, uint[] memory carolValues }
    ~[memoryFieldWriteUnfoldSource]~>
      dl!{ ⟨ uint se1 = carolValues[i]; carol.age = se1; ⟩ true
        where Person memory carol, uint[] memory carolValues } := rfl

-- printed `memoryIndexReadArrayValue`
example : dl!{ ⟨ v = carolValues[i]; ⟩ true where uint[] memory carolValues }
    ~[memoryIndexReadHeap]~>
      dl!{ { v := read(memory, carolValues[i]) } ⟨⟩ true where uint[] memory carolValues } := rfl

/-! ### Compound assignment and increment -/

example : dl!{ ⟨ carol.age += ageVal; ⟩ true where Person memory carol }
    ~[memoryFieldOpAssign]~>
      dl!{ { memory := write(memory, carol.age, read(memory, carol.age) + ageVal) } ⟨⟩ true
        where Person memory carol } := rfl

-- printed `memoryFieldDivAssign`; the quotient is no term `dl!{ … }` writes, so the line is left open.
example : ∃ ψ, dl!{ ⟨ carol.age /= ageVal; ⟩ true where Person memory carol }
    ~[memoryFieldOpAssign]~> ψ := ⟨_, rfl⟩

-- printed `memoryFieldPostincrement`
example : dl!{ ⟨ carol.age++; ⟩ true where Person memory carol }
    ~[memoryFieldIncrement]~>
      dl!{ { memory := write(memory, carol.age, read(memory, carol.age) + 1) } ⟨⟩ true
        where Person memory carol } := rfl

example : dl!{ ⟨ carolValues[i] += val; ⟩ true where uint[] memory carolValues }
    ~[memoryIndexArrayOpAssign]~>
      dl!{ { memory := write(memory, carolValues[i], read(memory, carolValues[i]) + val) } ⟨⟩ true
        where uint[] memory carolValues } := rfl

end Solidity.Examples.Chains.MemoryCoverage
