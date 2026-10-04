import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close

/-!
# Memory rule coverage: one chain per rule

The paper's coverage table (`sections/memory-coverage.tex`), one row per rule: a statement, run as a chain
term (`Calculus/Chains.lean`, `.claude/rules/derivations.md`) over any modality `m` and postcondition `φ`.
Each theorem is named after the row's rule as the paper prints it (with a suffix where two rows share one);
where Lean's rule has another name, a comment says so.  The row's rule is the chain's one printed `⇝`: its
own `~[r]~>` link, or, where it ends the program, one `~*>` with the `emptyModality` after it (the paper never
shows the `⟨[ ]⟩` line), so that such a row is a lone `~*>`, a `def`.  The steps the table does not print are
grouped as `#chain` groups them (a declaration with the binding it leaves is one `~*>`); past the program the
stack merges and every read is resolved one law a link, every capture kept to the last line, which
`#last_line` checks.

A memory object is declared by a `where` clause, `Person memory carol`, as the printer writes it
(`Calculus/Notation.lean`), on each line that still runs a program, and on each line whose update binds or
writes a reference (`{ carol := david }`, `write(memory, carol.account, acc)`): without it the reference reads
as a value, and the line is another one.  `#chain` prints these lines without the clause.  The row
`Person memory carol;` declares its object in the program.  A free value parameter (`balanceVal`, `ageVal`, `val`, `i`, `n`) gets a small int in an
update on the first line, and a member the statement reads a value there,
`{ memory := write(memory, carol.age, 42) }`, so a value read ends at a literal.  A memory reference (`tok`,
`acc`, `carolToken`) has no literal and stays free.

The literal laws and `findOnSave` rewrite inside a memory term too (`Upd.rwEv`), so a sum written to memory
folds (`write(…, carol.age, 47)`), an index `2 + 1` in a memory address folds to `3` (and the read at it
resolves), and a storage read written to memory resolves.  What has no literal: a memory reference (a struct
or reference write, an alias, an allocation, a delete).

Stand-ins: `carol.account.values` and `carol.account.tokens` are `basket.items` and `bucket.tokens`
(`Account` has neither member).  A statement holding a call (`makeValue()`) or a `++` in an operand is the
elaborator's first step, an equation, not a rule: the row states the equation, and the chain after it runs
the statement.
-/

namespace Solidity.Examples.Chains.MemoryCoverage

/-- Memory needs no state; `makeValue()` is the call of its row. -/
def MemCoverage : Contract := contract!{
  uint total;
  function makeValue() returns (uint) { return total; }
}

local instance : InContract := ⟨MemCoverage⟩

section
variable (m : Modality) (φ : Post MemCoverage)

/-! ### Field writes -/

/-- `carol.account.balance = balanceVal;` with `balanceVal` 10. -/
theorem memoryFieldWrite_unfold_leftFst :
    dl![m]{ { balanceVal := 10 } ⟨[ carol.account.balance = balanceVal; ]⟩ φ where Person memory carol }
    ~[memoryFieldWrite_unfold_leftFst]~> dl![m]{ { balanceVal := 10 }
        ⟨[ Account memory mv1 = carol.account; mv1.balance = balanceVal; ]⟩ φ where Person memory carol }
    ~*> dl![m]{ { balanceVal := 10 } { mv1 := read(memory, carol.account) } ⟨[ mv1.balance = balanceVal; ]⟩ φ
        where Person memory carol }
    ~*> dl![m]{ { balanceVal := 10 } { mv1 := read(memory, carol.account) }
        { memory := write(memory, mv1.balance, balanceVal) } φ }
    ~[sequentialToParallel]~> dl![m]{ { balanceVal := 10 ‖ mv1 := read(memory, carol.account) ‖
        memory := write(memory, read(memory, carol.account).balance, 10) } φ } := by
  sol_chain
#last_line memoryFieldWrite_unfold_leftFst

-- Lean's `memoryFieldWrite_unfold_leftFst`.
/-- `carol.account.token = tok;`, the reference `tok` written through the alias. -/
theorem memoryFieldWriteMemRef_unfold_leftFst :
    dl![m]{ ⟨[ carol.account.token = tok; ]⟩ φ where Person memory carol, Token memory tok }
    ~[memoryFieldWrite_unfold_leftFst]~> dl![m]{ ⟨[ Account memory mv1 = carol.account; mv1.token = tok; ]⟩ φ
        where Person memory carol, Token memory tok }
    ~*> dl![m]{ { mv1 := read(memory, carol.account) } ⟨[ mv1.token = tok; ]⟩ φ
        where Person memory carol, Token memory tok }
    ~*> dl![m]{ { mv1 := read(memory, carol.account) } { memory := write(memory, mv1.token, tok) } φ
        where Token memory tok }
    ~[sequentialToParallel]~> dl![m]{ { mv1 := read(memory, carol.account) ‖
        memory := write(memory, read(memory, carol.account).token, tok) } φ where Token memory tok } := by
  sol_chain
#last_line memoryFieldWriteMemRef_unfold_leftFst

/-- `carol.age = ageVal + 1;` with `ageVal` 42: the source captured, the capture and the value written
folded to 43. -/
theorem memoryFieldWriteUnfoldSource :
    dl![m]{ { ageVal := 42 } ⟨[ carol.age = ageVal + 1; ]⟩ φ where Person memory carol }
    ~[memoryFieldWriteUnfoldSource]~> dl![m]{ { ageVal := 42 } ⟨[ uint se1 = ageVal + 1; carol.age = se1; ]⟩ φ
        where Person memory carol }
    ~*> dl![m]{ { ageVal := 42 } { se1 := ageVal + 1 } ⟨[ carol.age = se1; ]⟩ φ where Person memory carol }
    ~*> dl![m]{ { ageVal := 42 } { se1 := ageVal + 1 } { memory := write(memory, carol.age, se1) } φ }
    ~[sequentialToParallel]~> dl![m]{ { ageVal := 42 ‖ se1 := 42 + 1 ‖ memory := write(memory, carol.age, 42 + 1) } φ }
    ~[add_literals]~> dl![m]{ { ageVal := 42 ‖ se1 := 43 ‖ memory := write(memory, carol.age, 43) } φ } := by
  sol_chain
#last_line memoryFieldWriteUnfoldSource

-- Lean's `memoryFieldWriteCopy`: a memory path is a source as it stands.
/-- `carol.account = david.account;`: the identity `david.account` holds is written, which has no literal. -/
def memoryFieldWriteCaptureSrc :
    dl![m]{ ⟨[ carol.account = david.account; ]⟩ φ where Person memory carol, Person memory david }
    ~*> dl![m]{ { memory := write(memory, carol.account, read(memory, david.account)) } φ
        where Person memory carol, Person memory david } := by
  sol_chain
#last_line memoryFieldWriteCaptureSrc

-- Lean's `memoryFieldWriteCopy`.
/-- `carol.account = acc;`: the reference `acc` is written. -/
def memoryFieldWrite :
    dl![m]{ ⟨[ carol.account = acc; ]⟩ φ where Person memory carol, Account memory acc }
    ~*> dl![m]{ { memory := write(memory, carol.account, acc) } φ
        where Person memory carol, Account memory acc } := by
  sol_chain
#last_line memoryFieldWrite

-- Lean's `memoryFieldWriteStore`.
/-- `carol.age = ageVal;` with `ageVal` 42. -/
theorem memoryFieldWrite_value :
    dl![m]{ { ageVal := 42 } ⟨[ carol.age = ageVal; ]⟩ φ where Person memory carol }
    ~*> dl![m]{ { ageVal := 42 } { memory := write(memory, carol.age, ageVal) } φ }
    ~[sequentialToParallel]~> dl![m]{ { ageVal := 42 ‖ memory := write(memory, carol.age, 42) } φ } := by
  sol_chain
#last_line memoryFieldWrite_value

/-! ### Aliases, declarations and allocation -/

/-- `carol = david;`: the root is rebound to `david`'s identity. -/
def memoryRootAlias :
    dl![m]{ ⟨[ carol = david; ]⟩ φ where Person memory carol, Person memory david }
    ~*> dl![m]{ { carol := david } φ where Person memory carol, Person memory david } := by
  sol_chain
#last_line memoryRootAlias

/-- `Account memory acc = carol.account;`: the declaration dropped, then the alias bound. -/
theorem memoryLocalDeclInitDrop :
    dl![m]{ ⟨[ Account memory acc = carol.account; ]⟩ φ where Person memory carol }
    ~[memoryLocalDeclInitDrop]~> dl![m]{ ⟨[ acc = carol.account; ]⟩ φ
        where Person memory carol, Account memory acc }
    ~*> dl![m]{ { acc := read(memory, carol.account) } φ where Person memory carol, Account memory acc } := by
  sol_chain
#last_line memoryLocalDeclInitDrop

/-- `Person memory carol;`: a fresh object, its identity bound to `carol`. -/
def memoryReferenceDeclFreshAlloc :
    dl![m]{ ⟨[ Person memory carol; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } φ } := by
  sol_chain
#last_line memoryReferenceDeclFreshAlloc

/-- `xs = new uint[](n);` with `n` 3. -/
theorem memoryArrayFreshAlloc :
    dl![m]{ { n := 3 } ⟨[ xs = new uint[](n); ]⟩ φ where uint[] memory xs }
    ~*> dl![m]{ { n := 3 }
        { xs := freshId(copySt(memory, newArr(uint[], n))) ‖ memory := copySt(memory, newArr(uint[], n)) } φ }
    ~[sequentialToParallel]~> dl![m]{ { n := 3 ‖ xs := freshId(copySt(memory, newArr(uint[], 3))) ‖
        memory := copySt(memory, newArr(uint[], 3)) } φ } := by
  sol_chain
#last_line memoryArrayFreshAlloc

-- `basket.items` for `carol.account.values`.
/-- `basket.items = new uint[](n);` with `n` 3: the array allocated into a local, then written. -/
theorem newArrayCapture :
    dl![m]{ { n := 3 } ⟨[ basket.items = new uint[](n); ]⟩ φ where Basket memory basket }
    ~[newArrayCapture]~> dl![m]{ { n := 3 } ⟨[ uint[] memory mv1 = new uint[](n); basket.items = mv1; ]⟩ φ
        where Basket memory basket }
    ~*> dl![m]{ { n := 3 }
        { mv1 := freshId(copySt(memory, newArr(uint[], n))) ‖ memory := copySt(memory, newArr(uint[], n)) }
          ⟨[ basket.items = mv1; ]⟩ φ where Basket memory basket }
    ~*> dl![m]{ { n := 3 }
        { mv1 := freshId(copySt(memory, newArr(uint[], n))) ‖ memory := copySt(memory, newArr(uint[], n)) }
          { memory := write(memory, basket.items, mv1) } φ }
    ~[sequentialToParallel]~> dl![m]{ { n := 3 ‖ mv1 := freshId(copySt(memory, newArr(uint[], 3))) ‖
        memory := write(copySt(memory, newArr(uint[], 3)), basket.items, freshId(copySt(memory, newArr(uint[], 3)))) }
          φ } := by
  sol_chain
#last_line newArrayCapture

/-! ### Field reads -/

/-- `v = carol.account.balance;` from a memory where it is 10: past the merge the read of `carol.account`
passes the write to `balance` (`readWriteDifferentIdentity`), and the member read is that write's value
(`readOnWrite`). -/
theorem memoryFieldRead_unfold_rightFst :
    dl![m]{ { memory := write(memory, read(memory, carol.account).balance, 10) } ⟨[ v = carol.account.balance; ]⟩ φ
        where Person memory carol }
    ~[memoryFieldRead_unfold_rightFst]~> dl![m]{
        { memory := write(memory, read(memory, carol.account).balance, 10) }
          ⟨[ Account memory mv1 = carol.account; v = mv1.balance; ]⟩ φ where Person memory carol }
    ~*> dl![m]{
        { memory := write(memory, read(memory, carol.account).balance, 10) }
          { mv1 := read(memory, carol.account) } ⟨[ v = mv1.balance; ]⟩ φ where Person memory carol }
    ~*> dl![m]{
        { memory := write(memory, read(memory, carol.account).balance, 10) }
          { mv1 := read(memory, carol.account) } { v := read(memory, mv1.balance) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { memory := write(memory, read(memory, carol.account).balance, 10) ‖
            mv1 := read(write(memory, read(memory, carol.account).balance, 10), carol.account) ‖
            v :=
              read(write(memory, read(memory, carol.account).balance, 10),
                read(write(memory, read(memory, carol.account).balance, 10), carol.account).balance) }
          φ }
    ~[readWriteDifferentIdentity]~> dl![m]{
        { memory := write(memory, read(memory, carol.account).balance, 10) ‖ mv1 := read(memory, carol.account) ‖
            v := read(write(memory, read(memory, carol.account).balance, 10), read(memory, carol.account).balance) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { memory := write(memory, read(memory, carol.account).balance, 10) ‖ mv1 := read(memory, carol.account) ‖
            v := 10 }
          φ } := by
  sol_chain
#last_line memoryFieldRead_unfold_rightFst

/-- `carolAcc = david.account;`: the identity `david.account` holds is bound. -/
def memoryFieldReadAliasRoot :
    dl![m]{ ⟨[ carolAcc = david.account; ]⟩ φ where Person memory david, Account memory carolAcc }
    ~*> dl![m]{ { carolAcc := read(memory, david.account) } φ
        where Person memory david, Account memory carolAcc } := by
  sol_chain
#last_line memoryFieldReadAliasRoot

-- Lean's `memoryFieldWrite_unfold_leftFst`: the strategy unfolds the target first, and the source read is
-- captured by `memoryFieldWriteUnfoldSource`.
/-- `carol.account.balance = acc.balance;` from a memory where `acc.balance` is 10. -/
theorem memoryFieldRead_unfold_rightSndResult :
    dl![m]{ { memory := write(memory, acc.balance, 10) } ⟨[ carol.account.balance = acc.balance; ]⟩ φ
        where Person memory carol, Account memory acc }
    ~[memoryFieldWrite_unfold_leftFst]~> dl![m]{ { memory := write(memory, acc.balance, 10) }
        ⟨[ Account memory mv1 = carol.account; mv1.balance = acc.balance; ]⟩ φ
        where Person memory carol, Account memory acc }
    ~*> dl![m]{ { memory := write(memory, acc.balance, 10) } { mv1 := read(memory, carol.account) }
        ⟨[ mv1.balance = acc.balance; ]⟩ φ where Person memory carol, Account memory acc }
    ~[memoryFieldWriteUnfoldSource]~> dl![m]{ { memory := write(memory, acc.balance, 10) }
        { mv1 := read(memory, carol.account) } ⟨[ uint se2 = acc.balance; mv1.balance = se2; ]⟩ φ
        where Person memory carol, Account memory acc }
    ~*> dl![m]{ { memory := write(memory, acc.balance, 10) } { mv1 := read(memory, carol.account) }
        { se2 := read(memory, acc.balance) } ⟨[ mv1.balance = se2; ]⟩ φ
        where Person memory carol, Account memory acc }
    ~*> dl![m]{ { memory := write(memory, acc.balance, 10) } { mv1 := read(memory, carol.account) }
        { se2 := read(memory, acc.balance) } { memory := write(memory, mv1.balance, se2) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { mv1 := read(write(memory, acc.balance, 10), carol.account) ‖
            se2 := read(write(memory, acc.balance, 10), acc.balance) ‖
            memory :=
              write(write(memory, acc.balance, 10), read(write(memory, acc.balance, 10), carol.account).balance,
                read(write(memory, acc.balance, 10), acc.balance)) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { mv1 := read(write(memory, acc.balance, 10), carol.account) ‖ se2 := 10 ‖
            memory := write(write(memory, acc.balance, 10), read(write(memory, acc.balance, 10), carol.account).balance, 10) }
          φ }
    ~[readWriteDifferentIdentity]~> dl![m]{
        { mv1 := read(memory, carol.account) ‖ se2 := 10 ‖
            memory := write(write(memory, acc.balance, 10), read(memory, carol.account).balance, 10) }
          φ } := by
  sol_chain
#last_line memoryFieldRead_unfold_rightSndResult

/-- `carol.age = acc.balance;` from a memory where `acc.balance` is 10: the value-source rule captures the
read. -/
theorem memoryFieldWriteUnfoldSource_read :
    dl![m]{ { memory := write(memory, acc.balance, 10) } ⟨[ carol.age = acc.balance; ]⟩ φ
        where Person memory carol, Account memory acc }
    ~[memoryFieldWriteUnfoldSource]~> dl![m]{ { memory := write(memory, acc.balance, 10) }
        ⟨[ uint se1 = acc.balance; carol.age = se1; ]⟩ φ where Person memory carol, Account memory acc }
    ~*> dl![m]{ { memory := write(memory, acc.balance, 10) } { se1 := read(memory, acc.balance) }
        ⟨[ carol.age = se1; ]⟩ φ where Person memory carol, Account memory acc }
    ~*> dl![m]{ { memory := write(memory, acc.balance, 10) } { se1 := read(memory, acc.balance) }
        { memory := write(memory, carol.age, se1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { se1 := read(write(memory, acc.balance, 10), acc.balance) ‖
            memory := write(write(memory, acc.balance, 10), carol.age, read(write(memory, acc.balance, 10), acc.balance)) }
          φ }
    ~[readOnWrite]~> dl![m]{ { se1 := 10 ‖ memory := write(write(memory, acc.balance, 10), carol.age, 10) } φ } := by
  sol_chain
#last_line memoryFieldWriteUnfoldSource_read

/-- `v = carol.age;` from a memory where it is 42. -/
theorem memoryFieldReadHeap :
    dl![m]{ { memory := write(memory, carol.age, 42) } ⟨[ v = carol.age; ]⟩ φ where Person memory carol }
    ~*> dl![m]{ { memory := write(memory, carol.age, 42) } { v := read(memory, carol.age) } φ }
    ~[sequentialToParallel]~> dl![m]{ { memory := write(memory, carol.age, 42) ‖
        v := read(write(memory, carol.age, 42), carol.age) } φ }
    ~[readOnWrite]~> dl![m]{ { memory := write(memory, carol.age, 42) ‖ v := 42 } φ } := by
  sol_chain
#last_line memoryFieldReadHeap

-- Lean's `memoryRootAlias`.
/-- `carolAlias = carol;`: the alias is bound to `carol`'s identity. -/
def memoryRootAlias_alias :
    dl![m]{ ⟨[ carolAlias = carol; ]⟩ φ where Person memory carol, Person memory carolAlias }
    ~*> dl![m]{ { carolAlias := carol } φ where Person memory carol, Person memory carolAlias } := by
  sol_chain
#last_line memoryRootAlias_alias

/-! ### `delete` -/

/-- `delete carol;`: `carol` is rebound to a fresh object. -/
def memoryRootDeleteFreshRebind :
    dl![m]{ ⟨[ delete carol; ]⟩ φ where Person memory carol }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } φ } := by
  sol_chain
#last_line memoryRootDeleteFreshRebind

/-- `delete carol.age;`: the member is written its default. -/
def memoryFieldDeletePrimitive :
    dl![m]{ ⟨[ delete carol.age; ]⟩ φ where Person memory carol }
    ~*> dl![m]{ { memory := write(memory, carol.age, 0) } φ } := by
  sol_chain
#last_line memoryFieldDeletePrimitive

/-- `delete carol.account;`: the member is written a fresh object. -/
def memoryFieldDeleteReference :
    dl![m]{ ⟨[ delete carol.account; ]⟩ φ where Person memory carol }
    ~*>
      dl![m]{ { memory := write(addM(memory, Account), carol.account, freshId(addM(memory, Account))) } φ } := by
  sol_chain
#last_line memoryFieldDeleteReference

/-- `delete carolValues[i];` with `i` 2. -/
theorem memoryIndexDeletePrimitive :
    dl![m]{ { i := 2 } ⟨[ delete carolValues[i]; ]⟩ φ where uint[] memory carolValues }
    ~*> dl![m]{ { i := 2 } { memory := write(memory, carolValues[i], 0) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[2], 0) } φ } := by
  sol_chain
#last_line memoryIndexDeletePrimitive

/-- `delete carolTokens[i];` with `i` 2. -/
theorem memoryIndexDeleteReference :
    dl![m]{ { i := 2 } ⟨[ delete carolTokens[i]; ]⟩ φ where Token[] memory carolTokens }
    ~*> dl![m]{ { i := 2 }
        { memory := write(addM(memory, Token), carolTokens[i], freshId(addM(memory, Token))) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖
        memory := write(addM(memory, Token), carolTokens[2], freshId(addM(memory, Token))) } φ } := by
  sol_chain
#last_line memoryIndexDeleteReference

/-- `delete carol.account.token;` -/
theorem memoryFieldDelete_unfold_leftFst :
    dl![m]{ ⟨[ delete carol.account.token; ]⟩ φ where Person memory carol }
    ~[memoryFieldDelete_unfold_leftFst]~> dl![m]{ ⟨[ Account memory mv1 = carol.account; delete mv1.token; ]⟩ φ
        where Person memory carol }
    ~*> dl![m]{ { mv1 := read(memory, carol.account) } ⟨[ delete mv1.token; ]⟩ φ where Person memory carol }
    ~*> dl![m]{ { mv1 := read(memory, carol.account) }
        { memory := write(addM(memory, Token), mv1.token, freshId(addM(memory, Token))) } φ }
    ~[sequentialToParallel]~> dl![m]{ { mv1 := read(memory, carol.account) ‖
        memory := write(addM(memory, Token), read(memory, carol.account).token, freshId(addM(memory, Token))) } φ } := by
  sol_chain
#last_line memoryFieldDelete_unfold_leftFst

-- `bucket.tokens` for `carol.account.tokens`.
/-- `delete bucket.tokens[i];` with `i` 2. -/
theorem memoryIndexDelete_unfold_leftFst :
    dl![m]{ { i := 2 } ⟨[ delete bucket.tokens[i]; ]⟩ φ where TokenBucket memory bucket }
    ~[memoryIndexDelete_unfold_leftFst]~> dl![m]{ { i := 2 } ⟨[ Token[] memory mv1 = bucket.tokens; delete mv1[i]; ]⟩ φ
        where TokenBucket memory bucket }
    ~*> dl![m]{ { i := 2 } { mv1 := read(memory, bucket.tokens) } ⟨[ delete mv1[i]; ]⟩ φ
        where TokenBucket memory bucket }
    ~*> dl![m]{ { i := 2 } { mv1 := read(memory, bucket.tokens) }
        { memory := write(addM(memory, Token), mv1[i], freshId(addM(memory, Token))) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ mv1 := read(memory, bucket.tokens) ‖
        memory := write(addM(memory, Token), read(memory, bucket.tokens)[2], freshId(addM(memory, Token))) } φ } := by
  sol_chain
#last_line memoryIndexDelete_unfold_leftFst

/-! ### Index writes -/

-- The receiver and the `++i` are captured by the elaborator; `basket.items` for
-- `carol.account.values`.
example : dl!{ ⟨ basket.items[++i] = val; ⟩ true where Basket memory basket }
    = dl!{ ⟨ uint se1 = val; uint[] memory mv2 = basket.items; uint se3; se3 = ++i; mv2[se3] = se1; ⟩ true
        where Basket memory basket } := rfl

/-- `basket.items[++i] = val;` with `i` 2 and `val` 7: the captures, the increment, the write at `2 + 1`,
folded to `3`. -/
theorem memoryIndexWriteCaptureAllComplexRecv :
    dl![m]{ { i := 2 ‖ val := 7 } ⟨[ basket.items[++i] = val; ]⟩ φ where Basket memory basket }
    ~*> dl![m]{ { i := 2 ‖ val := 7 } { se1 := val } { mv2 := read(memory, basket.items) } { se3 := 0 }
        ⟨[ se3 = ++i; mv2[se3] = se1; ]⟩ φ where Basket memory basket }
    ~[localAssignIncrement]~> dl![m]{ { i := 2 ‖ val := 7 } { se1 := val } { mv2 := read(memory, basket.items) }
        { se3 := 0 } { i := i + 1 ‖ se3 := i + 1 } ⟨[ mv2[se3] = se1; ]⟩ φ where Basket memory basket }
    ~*> dl![m]{ { i := 2 ‖ val := 7 } { se1 := val } { mv2 := read(memory, basket.items) } { se3 := 0 }
        { i := i + 1 ‖ se3 := i + 1 } { memory := write(memory, mv2[se3], se1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ val := 7 ‖ se1 := 7 ‖ mv2 := read(memory, basket.items) ‖ se3 := 0 ‖ i := 2 + 1 ‖ se3 := 2 + 1 ‖
            memory := write(memory, read(memory, basket.items)[2 + 1], 7) }
          φ }
    ~[add_literals]~> dl![m]{
        { i := 2 ‖ val := 7 ‖ se1 := 7 ‖ mv2 := read(memory, basket.items) ‖ se3 := 0 ‖ i := 3 ‖ se3 := 3 ‖
            memory := write(memory, read(memory, basket.items)[3], 7) }
          φ } := by
  sol_chain
#last_line memoryIndexWriteCaptureAllComplexRecv

-- `bucket.tokens` for `carol.account.tokens`.
/-- `bucket.tokens[i] = carolToken;` with `i` 2. -/
theorem memoryIndexWriteMemRefCaptureAllComplexRecv :
    dl![m]{ { i := 2 } ⟨[ bucket.tokens[i] = carolToken; ]⟩ φ where TokenBucket memory bucket, Token memory carolToken }
    ~[memoryIndexWriteMemRefCaptureAllComplexRecv]~> dl![m]{ { i := 2 }
        ⟨[ Token[] memory mv1 = bucket.tokens; uint ie1 = i; mv1[ie1] = carolToken; ]⟩ φ
        where TokenBucket memory bucket, Token memory carolToken }
    ~*> dl![m]{ { i := 2 } { mv1 := read(memory, bucket.tokens) } { ie1 := i } ⟨[ mv1[ie1] = carolToken; ]⟩ φ
        where TokenBucket memory bucket, Token memory carolToken }
    ~*> dl![m]{ { i := 2 } { mv1 := read(memory, bucket.tokens) } { ie1 := i }
        { memory := write(memory, mv1[ie1], carolToken) } φ where Token memory carolToken }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ mv1 := read(memory, bucket.tokens) ‖ ie1 := 2 ‖
        memory := write(memory, read(memory, bucket.tokens)[2], carolToken) } φ where Token memory carolToken } := by
  sol_chain
#last_line memoryIndexWriteMemRefCaptureAllComplexRecv

example : dl!{ ⟨ carolValues[++i] = val; ⟩ true where uint[] memory carolValues }
    = dl!{ ⟨ uint se1 = val; uint se2; se2 = ++i; carolValues[se2] = se1; ⟩ true
        where uint[] memory carolValues } := rfl

/-- `carolValues[++i] = val;` with `i` 2 and `val` 7: the write at `2 + 1`, folded to `3`. -/
theorem memoryIndexWriteCaptureAllNonSimpleIndex :
    dl![m]{ { i := 2 ‖ val := 7 } ⟨[ carolValues[++i] = val; ]⟩ φ where uint[] memory carolValues }
    ~*> dl![m]{ { i := 2 ‖ val := 7 } { se1 := val } { se2 := 0 } ⟨[ se2 = ++i; carolValues[se2] = se1; ]⟩ φ
        where uint[] memory carolValues }
    ~[localAssignIncrement]~> dl![m]{ { i := 2 ‖ val := 7 } { se1 := val } { se2 := 0 } { i := i + 1 ‖ se2 := i + 1 }
        ⟨[ carolValues[se2] = se1; ]⟩ φ where uint[] memory carolValues }
    ~*> dl![m]{ { i := 2 ‖ val := 7 } { se1 := val } { se2 := 0 } { i := i + 1 ‖ se2 := i + 1 }
        { memory := write(memory, carolValues[se2], se1) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ val := 7 ‖ se1 := 7 ‖ se2 := 0 ‖ i := 2 + 1 ‖ se2 := 2 + 1 ‖
        memory := write(memory, carolValues[2 + 1], 7) } φ }
    ~[add_literals]~> dl![m]{ { i := 2 ‖ val := 7 ‖ se1 := 7 ‖ se2 := 0 ‖ i := 3 ‖ se2 := 3 ‖ memory := write(memory, carolValues[3], 7) } φ } := by
  sol_chain
#last_line memoryIndexWriteCaptureAllNonSimpleIndex

example : dl!{ ⟨ carolTokens[++i] = carolToken; ⟩ true where Token[] memory carolTokens, Token memory carolToken }
    = dl!{ ⟨ uint se1; se1 = ++i; carolTokens[se1] = carolToken; ⟩ true
        where Token[] memory carolTokens, Token memory carolToken } := rfl

/-- `carolTokens[++i] = carolToken;` with `i` 2: the write at `2 + 1`, folded to `3`. -/
theorem memoryIndexWriteMemRefCaptureAllNonSimpleIndex :
    dl![m]{ { i := 2 } ⟨[ carolTokens[++i] = carolToken; ]⟩ φ
        where Token[] memory carolTokens, Token memory carolToken }
    ~[valueDeclSkip]~> dl![m]{ { i := 2 } { se1 := 0 } ⟨[ se1 = ++i; carolTokens[se1] = carolToken; ]⟩ φ
        where Token[] memory carolTokens, Token memory carolToken }
    ~[localAssignIncrement]~> dl![m]{ { i := 2 } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 }
        ⟨[ carolTokens[se1] = carolToken; ]⟩ φ where Token[] memory carolTokens, Token memory carolToken }
    ~*> dl![m]{ { i := 2 } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 }
        { memory := write(memory, carolTokens[se1], carolToken) } φ
        where Token[] memory carolTokens, Token memory carolToken }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ se1 := 0 ‖ i := 2 + 1 ‖ se1 := 2 + 1 ‖
        memory := write(memory, carolTokens[2 + 1], carolToken) } φ
        where Token[] memory carolTokens, Token memory carolToken }
    ~[add_literals]~> dl![m]{ { i := 2 ‖ se1 := 0 ‖ i := 3 ‖ se1 := 3 ‖ memory := write(memory, carolTokens[3], carolToken) } φ
        where Token[] memory carolTokens, Token memory carolToken } := by
  sol_chain
#last_line memoryIndexWriteMemRefCaptureAllNonSimpleIndex

-- The call is the elaborator's.
example : dl!{ ⟨ carolValues[i] = makeValue(); ⟩ true where uint[] memory carolValues }
    = dl!{ ⟨ uint se1; se1 = makeValue(); carolValues[i] = se1; ⟩ true where uint[] memory carolValues } := rfl

/-- `carolValues[i] = makeValue();` with `i` 2, from a storage where `total` is 7: the call's body inlined
(`functionBodyExpand`), its result written.  The captures and the value written resolve to 7. -/
theorem memoryIndexWriteUnfoldSource :
    dl![m]{ { i := 2 ‖ storage := store(storage, total, 7) } ⟨[ carolValues[i] = makeValue(); ]⟩ φ
        where uint[] memory carolValues }
    ~[valueDeclSkip]~> dl![m]{ { i := 2 ‖ storage := store(storage, total, 7) } { se1 := 0 }
        ⟨[ se1 = makeValue(); carolValues[i] = se1; ]⟩ φ where uint[] memory carolValues }
    ~[functionBodyExpand]~> dl![m]{ { i := 2 ‖ storage := store(storage, total, 7) } { se1 := 0 }
        ⟨[ uint se2; se2 = total; se1 = se2; carolValues[i] = se1; ]⟩ φ where uint[] memory carolValues }
    ~*> dl![m]{ { i := 2 ‖ storage := store(storage, total, 7) } { se1 := 0 } { se2 := 0 }
        { se2 := select(storage, total) } { se1 := se2 } ⟨[ carolValues[i] = se1; ]⟩ φ
        where uint[] memory carolValues }
    ~*> dl![m]{ { i := 2 ‖ storage := store(storage, total, 7) } { se1 := 0 } { se2 := 0 }
        { se2 := select(storage, total) } { se1 := se2 } { memory := write(memory, carolValues[i], se1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ storage := store(storage, total, 7) ‖ se1 := 0 ‖ se2 := 0 ‖
            se2 := select(store(storage, total, 7), total) ‖ se1 := select(store(storage, total, 7), total) ‖
            memory := write(memory, carolValues[2], select(store(storage, total, 7), total)) }
          φ }
    ~[findOnSave]~> dl![m]{
        { i := 2 ‖ storage := store(storage, total, 7) ‖ se1 := 0 ‖ se2 := 0 ‖ se2 := 7 ‖ se1 := 7 ‖
            memory := write(memory, carolValues[2], 7) }
          φ } := by
  sol_chain
#last_line memoryIndexWriteUnfoldSource

-- Lean's `memoryFieldRead_unfold_rightFst`: the receiver `david.account` is unfolded first.
/-- `carolTokens[i] = david.account.token;` with `i` 2: the identity the member holds is written. -/
theorem memoryIndexWriteMemRefRhsCapture :
    dl![m]{ { i := 2 } ⟨[ carolTokens[i] = david.account.token; ]⟩ φ
        where Token[] memory carolTokens, Person memory david }
    ~[memoryFieldRead_unfold_rightFst]~> dl![m]{ { i := 2 }
        ⟨[ Account memory mv1 = david.account; carolTokens[i] = mv1.token; ]⟩ φ
        where Token[] memory carolTokens, Person memory david }
    ~*> dl![m]{ { i := 2 } { mv1 := read(memory, david.account) } ⟨[ carolTokens[i] = mv1.token; ]⟩ φ
        where Token[] memory carolTokens, Person memory david }
    ~*> dl![m]{ { i := 2 } { mv1 := read(memory, david.account) }
        { memory := write(memory, carolTokens[i], read(memory, mv1.token)) } φ
        where Token[] memory carolTokens, Person memory david }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ mv1 := read(memory, david.account) ‖
        memory := write(memory, carolTokens[2], read(memory, read(memory, david.account).token)) } φ
        where Token[] memory carolTokens, Person memory david } := by
  sol_chain
#last_line memoryIndexWriteMemRefRhsCapture

-- Lean's `memoryIndexWriteCopy`.
/-- `carolTokens[i] = carolToken;` with `i` 2: the reference is written. -/
theorem memoryIndexWriteArray :
    dl![m]{ { i := 2 } ⟨[ carolTokens[i] = carolToken; ]⟩ φ
        where Token[] memory carolTokens, Token memory carolToken }
    ~*> dl![m]{ { i := 2 } { memory := write(memory, carolTokens[i], carolToken) } φ
        where Token[] memory carolTokens, Token memory carolToken }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ memory := write(memory, carolTokens[2], carolToken) } φ
        where Token[] memory carolTokens, Token memory carolToken } := by
  sol_chain
#last_line memoryIndexWriteArray

-- Lean's `memoryIndexWriteStore`.
/-- `carolValues[i] = val;` with `i` 2 and `val` 7. -/
theorem memoryIndexWriteArray_value :
    dl![m]{ { i := 2 ‖ val := 7 } ⟨[ carolValues[i] = val; ]⟩ φ where uint[] memory carolValues }
    ~*> dl![m]{ { i := 2 ‖ val := 7 } { memory := write(memory, carolValues[i], val) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ val := 7 ‖ memory := write(memory, carolValues[2], 7) } φ } := by
  sol_chain
#last_line memoryIndexWriteArray_value

/-! ### Index reads -/

-- `basket.items` for `carol.account.values`.
/-- `v = basket.items[i];` with `i` 2, from a memory where `basket.items[2]` is 7. -/
theorem memoryIndexRead_unfold_rightFst :
    dl![m]{ { i := 2 ‖ memory := write(memory, read(memory, basket.items)[2], 7) } ⟨[ v = basket.items[i]; ]⟩ φ
        where Basket memory basket }
    ~[memoryIndexRead_unfold_rightFst]~> dl![m]{ { i := 2 ‖ memory := write(memory, read(memory, basket.items)[2], 7) }
        ⟨[ uint[] memory mv1 = basket.items; v = mv1[i]; ]⟩ φ where Basket memory basket }
    ~*> dl![m]{ { i := 2 ‖ memory := write(memory, read(memory, basket.items)[2], 7) }
        { mv1 := read(memory, basket.items) } ⟨[ v = mv1[i]; ]⟩ φ where Basket memory basket }
    ~*> dl![m]{ { i := 2 ‖ memory := write(memory, read(memory, basket.items)[2], 7) }
        { mv1 := read(memory, basket.items) } { v := read(memory, mv1[i]) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ memory := write(memory, read(memory, basket.items)[2], 7) ‖
            mv1 := read(write(memory, read(memory, basket.items)[2], 7), basket.items) ‖
            v :=
              read(write(memory, read(memory, basket.items)[2], 7),
                read(write(memory, read(memory, basket.items)[2], 7), basket.items)[2]) }
          φ }
    ~[readWriteDifferentIdentity]~> dl![m]{
        { i := 2 ‖ memory := write(memory, read(memory, basket.items)[2], 7) ‖ mv1 := read(memory, basket.items) ‖
            v := read(write(memory, read(memory, basket.items)[2], 7), read(memory, basket.items)[2]) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { i := 2 ‖ memory := write(memory, read(memory, basket.items)[2], 7) ‖ mv1 := read(memory, basket.items) ‖
            v := 7 }
          φ } := by
  sol_chain
#last_line memoryIndexRead_unfold_rightFst

example : dl!{ ⟨ v = carolValues[++i]; ⟩ true where uint[] memory carolValues }
    = dl!{ ⟨ uint se1; se1 = ++i; v = carolValues[se1]; ⟩ true where uint[] memory carolValues } := rfl

/-- `v = carolValues[++i];` with `i` 2, from a memory where `carolValues[3]` is 7: the index folds to `3`,
and the read resolves to `7` (`readOnWrite`). -/
theorem memoryIndexRead_unfold_rightSndIndex :
    dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[3], 7) } ⟨[ v = carolValues[++i]; ]⟩ φ
        where uint[] memory carolValues }
    ~[valueDeclSkip]~> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[3], 7) } { se1 := 0 }
        ⟨[ se1 = ++i; v = carolValues[se1]; ]⟩ φ where uint[] memory carolValues }
    ~[localAssignIncrement]~> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[3], 7) } { se1 := 0 }
        { i := i + 1 ‖ se1 := i + 1 } ⟨[ v = carolValues[se1]; ]⟩ φ where uint[] memory carolValues }
    ~*> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[3], 7) } { se1 := 0 }
        { i := i + 1 ‖ se1 := i + 1 } { v := read(memory, carolValues[se1]) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[3], 7) ‖ se1 := 0 ‖ i := 2 + 1 ‖
        se1 := 2 + 1 ‖ v := read(write(memory, carolValues[3], 7), carolValues[2 + 1]) } φ }
    ~[add_literals]~> dl![m]{
        { i := 2 ‖ memory := write(memory, carolValues[3], 7) ‖ se1 := 0 ‖ i := 3 ‖ se1 := 3 ‖
            v := read(write(memory, carolValues[3], 7), carolValues[3]) }
          φ }
    ~[readOnWrite]~> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[3], 7) ‖ se1 := 0 ‖ i := 3 ‖ se1 := 3 ‖ v := 7 } φ } := by
  sol_chain
#last_line memoryIndexRead_unfold_rightSndIndex

/-- `carolToken = davidTokens[i];` with `i` 2: the identity at the index is bound. -/
theorem memoryIndexReadAliasRoot :
    dl![m]{ { i := 2 } ⟨[ carolToken = davidTokens[i]; ]⟩ φ
        where Token[] memory davidTokens, Token memory carolToken }
    ~*> dl![m]{ { i := 2 } { carolToken := read(memory, davidTokens[i]) } φ
        where Token[] memory davidTokens, Token memory carolToken }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ carolToken := read(memory, davidTokens[2]) } φ
        where Token[] memory davidTokens, Token memory carolToken } := by
  sol_chain
#last_line memoryIndexReadAliasRoot

-- Lean's `memoryFieldWriteUnfoldSource`.
/-- `carol.age = carolValues[i];` with `i` 2, from a memory where `carolValues[2]` is 7. -/
theorem memoryIndexRead_unfold_rightSndResult :
    dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[2], 7) } ⟨[ carol.age = carolValues[i]; ]⟩ φ
        where Person memory carol, uint[] memory carolValues }
    ~[memoryFieldWriteUnfoldSource]~> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[2], 7) }
        ⟨[ uint se1 = carolValues[i]; carol.age = se1; ]⟩ φ where Person memory carol, uint[] memory carolValues }
    ~*> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[2], 7) } { se1 := read(memory, carolValues[i]) }
        ⟨[ carol.age = se1; ]⟩ φ where Person memory carol, uint[] memory carolValues }
    ~*> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[2], 7) } { se1 := read(memory, carolValues[i]) }
        { memory := write(memory, carol.age, se1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ se1 := read(write(memory, carolValues[2], 7), carolValues[2]) ‖
            memory :=
              write(write(memory, carolValues[2], 7), carol.age, read(write(memory, carolValues[2], 7), carolValues[2])) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { i := 2 ‖ se1 := 7 ‖ memory := write(write(memory, carolValues[2], 7), carol.age, 7) } φ } := by
  sol_chain
#last_line memoryIndexRead_unfold_rightSndResult

/-- `v = carolValues[i];` with `i` 2, from a memory where `carolValues[2]` is 7. -/
theorem memoryIndexReadHeap :
    dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[2], 7) } ⟨[ v = carolValues[i]; ]⟩ φ
        where uint[] memory carolValues }
    ~*> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[2], 7) }
        { v := read(memory, carolValues[i]) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[2], 7) ‖
        v := read(write(memory, carolValues[2], 7), carolValues[2]) } φ }
    ~[readOnWrite]~> dl![m]{ { i := 2 ‖ memory := write(memory, carolValues[2], 7) ‖ v := 7 } φ } := by
  sol_chain
#last_line memoryIndexReadHeap

/-! ### Compound assignment and increment -/

/-- `carol.age += ageVal;` with `ageVal` 5, from a memory where `carol.age` is 42: the sum written folds
to `47`. -/
theorem memoryFieldOpAssign :
    dl![m]{ { ageVal := 5 ‖ memory := write(memory, carol.age, 42) } ⟨[ carol.age += ageVal; ]⟩ φ
        where Person memory carol }
    ~*> dl![m]{ { ageVal := 5 ‖ memory := write(memory, carol.age, 42) }
        { memory := write(memory, carol.age, read(memory, carol.age) + ageVal) } φ }
    ~[sequentialToParallel]~> dl![m]{ { ageVal := 5 ‖
        memory := write(write(memory, carol.age, 42), carol.age, read(write(memory, carol.age, 42), carol.age) + 5) } φ }
    ~[readOnWrite]~> dl![m]{ { ageVal := 5 ‖ memory := write(write(memory, carol.age, 42), carol.age, 42 + 5) } φ }
    ~[add_literals]~> dl![m]{ { ageVal := 5 ‖ memory := write(write(memory, carol.age, 42), carol.age, 47) } φ } := by
  sol_chain
#last_line memoryFieldOpAssign

-- Lean's `memoryFieldOpAssign`: the quotient is written, and a divisor of `0` halts in the update.
/-- `carol.age /= ageVal;` with `ageVal` 2, from a memory where `carol.age` is 42: the quotient written
folds to `21` (`div_literals`). -/
theorem memoryFieldDivAssign :
    dl![m]{ { ageVal := 2 ‖ memory := write(memory, carol.age, 42) } ⟨[ carol.age /= ageVal; ]⟩ φ
        where Person memory carol }
    ~*> dl![m]{ { ageVal := 2 ‖ memory := write(memory, carol.age, 42) }
        { memory := write(memory, carol.age, read(memory, carol.age) / ageVal) } φ }
    ~[sequentialToParallel]~> dl![m]{ { ageVal := 2 ‖
        memory := write(write(memory, carol.age, 42), carol.age, read(write(memory, carol.age, 42), carol.age) / 2) } φ }
    ~[readOnWrite]~> dl![m]{ { ageVal := 2 ‖ memory := write(write(memory, carol.age, 42), carol.age, 42 / 2) } φ }
    ~[div_literals]~> dl![m]{ { ageVal := 2 ‖ memory := write(write(memory, carol.age, 42), carol.age, 21) } φ } := by
  sol_chain
#last_line memoryFieldDivAssign

-- Lean's `memoryFieldIncrement`.
/-- `carol.age++;` from a memory where `carol.age` is 42: the sum written folds to `43`. -/
theorem memoryFieldIncrement :
    dl![m]{ { memory := write(memory, carol.age, 42) } ⟨[ carol.age++; ]⟩ φ where Person memory carol }
    ~*> dl![m]{ { memory := write(memory, carol.age, 42) }
        { memory := write(memory, carol.age, read(memory, carol.age) + 1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { memory := write(write(memory, carol.age, 42), carol.age, read(write(memory, carol.age, 42), carol.age) + 1) } φ }
    ~[readOnWrite]~> dl![m]{ { memory := write(write(memory, carol.age, 42), carol.age, 42 + 1) } φ }
    ~[add_literals]~> dl![m]{ { memory := write(write(memory, carol.age, 42), carol.age, 43) } φ } := by
  sol_chain
#last_line memoryFieldIncrement

/-- `carolValues[i] += val;` with `i` 2 and `val` 7, from a memory where `carolValues[2]` is 10: the sum
written folds to `17`. -/
theorem memoryIndexArrayOpAssign :
    dl![m]{ { i := 2 ‖ val := 7 ‖ memory := write(memory, carolValues[2], 10) } ⟨[ carolValues[i] += val; ]⟩ φ
        where uint[] memory carolValues }
    ~*> dl![m]{ { i := 2 ‖ val := 7 ‖ memory := write(memory, carolValues[2], 10) }
        { memory := write(memory, carolValues[i], read(memory, carolValues[i]) + val) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ val := 7 ‖
        memory := write(write(memory, carolValues[2], 10), carolValues[2],
          read(write(memory, carolValues[2], 10), carolValues[2]) + 7) } φ }
    ~[readOnWrite]~> dl![m]{ { i := 2 ‖ val := 7 ‖
        memory := write(write(memory, carolValues[2], 10), carolValues[2], 10 + 7) } φ }
    ~[add_literals]~> dl![m]{ { i := 2 ‖ val := 7 ‖ memory := write(write(memory, carolValues[2], 10), carolValues[2], 17) } φ } := by
  sol_chain
#last_line memoryIndexArrayOpAssign

end
end Solidity.Examples.Chains.MemoryCoverage
