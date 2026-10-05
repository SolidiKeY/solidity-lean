import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close

/-!
# Storage rule coverage: one chain per rule

The paper's coverage table (`sections/storage-coverage.tex`), one row per rule: a statement, run as a chain
term (`Calculus/Chains.lean`, `.claude/rules/derivations.md`) over any modality `m` and postcondition `φ`.
Each theorem is named after the row's rule as the paper prints it.  The row's rule is the chain's one
printed `⇝`: its own `~[r]~>` link, or, where it ends the program, one `~*>` with the `emptyModality` after it
(the paper never shows the `⟨[ ]⟩` line), so that such a row is a lone `~*>`, a `def`.  The steps the table
does not print are grouped as `#chain` groups them (a declaration with the binding it leaves is one `~*>`);
past the program the stack merges and every read is resolved one law a link, every capture kept to the last
line, which `#last_line` checks.

A free parameter of the statement (`ageVal`, `i`, `id`, `tokRef`, …) and the storage it reads get a concrete
value in an update on the first line, so a value read ends at a literal.  Some reads have none: a struct
(`find(storage, bob)`), and a length (`tokens.length`), which has no spelling as a starting state.  A read at
an index checks its bound in the state it runs in (`values[2]@S`), which a law reads past only under the box,
so those rows are box chains; so are `require`'s, whose failing branch reverts: under `m` such a chain
stops at the `revert();`.  An `assert` reverts nowhere — its condition is owed under either modality
(`assertSimple`) — so its rows run under `m`.  A branch folds once its condition is a literal: `applyOnRigid` where the
update binds locals only, `applyOnPV` where it also writes the storage, then `concrete`.

Stand-ins: `alice.account.tokens` is `bucket.tokens`, and `alice.account.tokens[i] = tokVal;` a write of a
`uint` into `basket.items`; `tokVal`, `pVal` are `uint` where the row's source is a value (a `Token` or
`Person` value is no source here); `led` is the paper's `m`, which names the modality here.  A statement
holding a call (`makeValue()`) or a `++` in an operand is the elaborator's first step, an equation, not a
rule: the row states the equation, and the chain after it runs the statement.  A literal or negated
condition has no rule here (`if (true)` is `ifElseSplit`).
-/

namespace Solidity.Examples.Chains.StorageCoverage

/-- The state of the rows: `values` and `tokens` arrays, `ledgers` an array of mappings,
`tokenById` and `personById` mappings, `flag` a boolean. -/
def Coverage : Contract := contract!{
  uint total; uint age; bool flag; uint[] values; mapping(uint => uint) balances;
  Person alice; Person bob; Person[] people; mapping(uint => Person) personById;
  Token[] tokens; mapping(uint => Token) tokenById; mapping(uint => uint)[] ledgers;
  TokenBucket bucket; Basket basket; Account account;
  function makeValue() returns (uint) { return total; }
  function checkBalance() returns (bool) { return true; }
  function checkInvariant() returns (bool) { return true; }
}

local instance : InContract := ⟨Coverage⟩

section
variable (m : Modality) (φ : Post Coverage)

/-! ### Field and root writes -/

/-- `alice.account.balance = balanceVal;` with `balanceVal` 10. -/
theorem storageFieldWrite_unfold_leftFst :
    dl![m]{ { balanceVal := 10 } ⟨[ alice.account.balance = balanceVal; ]⟩ φ }
    ~[storageFieldWrite_unfold_leftFst]~> dl![m]{ { balanceVal := 10 }
        ⟨[ uint se1 = balanceVal; Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ }
    ~*> dl![m]{ { balanceVal := 10 } { se1 := balanceVal } { sp1 := alice.account } ⟨[ sp1.balance = se1; ]⟩ φ }
    ~*> dl![m]{ { balanceVal := 10 } { se1 := balanceVal } { sp1 := alice.account }
        { storage := save(storage, sp1.balance, se1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { balanceVal := 10 ‖ se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) }
          φ } := by
  sol_chain
#last_line storageFieldWrite_unfold_leftFst

/-- `alice.account = acc;` with `acc` bound to `bob.account`: the value found at the alias's path is written. -/
theorem storageFieldWriteCopySource :
    dl![m]{ { acc := bob.account } ⟨[ alice.account = acc; ]⟩ φ }
    ~*> dl![m]{ { acc := bob.account }
        { storage := save(storage, alice.account, find(storage, acc)) } φ }
    ~[sequentialToParallel]~> dl![m]{ { acc := bob.account ‖
        storage := save(storage, alice.account, find(storage, bob.account)) } φ } := by
  sol_chain
#last_line storageFieldWriteCopySource

/-- `alice.age = ageVal;` with `ageVal` 42. -/
theorem storageFieldWriteSave :
    dl![m]{ { ageVal := 42 } ⟨[ alice.age = ageVal; ]⟩ φ }
    ~*> dl![m]{ { ageVal := 42 } { storage := save(storage, alice.age, ageVal) } φ }
    ~[sequentialToParallel]~> dl![m]{ { ageVal := 42 ‖ storage := save(storage, alice.age, 42) } φ } := by
  sol_chain
#last_line storageFieldWriteSave

/-- `alice = bob;`: the struct `bob` is read, which has no literal. -/
def storageRootWriteCopySource :
    dl![m]{ ⟨[ alice = bob; ]⟩ φ }
    ~*> dl![m]{ { storage := store(storage, alice, find(storage, bob)) } φ } := by
  sol_chain
#last_line storageRootWriteCopySource

-- `pVal` is a `uint` and the root `total`: a `Person` value is no source.
/-- `total = pVal;` with `pVal` 7. -/
theorem storageRootWriteStore :
    dl![m]{ { pVal := 7 } ⟨[ total = pVal; ]⟩ φ }
    ~*> dl![m]{ { pVal := 7 } { storage := store(storage, total, pVal) } φ }
    ~[sequentialToParallel]~> dl![m]{ { pVal := 7 ‖ storage := store(storage, total, 7) } φ } := by
  sol_chain
#last_line storageRootWriteStore

/-! ### Declarations and rebinding -/

/-- `Account storage acc = alice.account;`: the declaration dropped, then the alias bound. -/
theorem storageLocalDeclInitDrop :
    dl![m]{ ⟨[ Account storage acc = alice.account; ]⟩ φ }
    ~[storageLocalDeclInitDrop]~> dl![m]{ ⟨[ acc = alice.account; ]⟩ φ }
    ~*> dl![m]{ { acc := alice.account } φ } := by
  sol_chain
#last_line storageLocalDeclInitDrop

/-- `uint v = alice.age;` from a storage where it is 42. -/
theorem localValueDeclInitDrop :
    dl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ uint v = alice.age; ]⟩ φ }
    ~[localValueDeclInitDrop]~> dl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ v = alice.age; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, 42) } { v := find(storage, alice.age) } φ }
    ~[sequentialToParallel]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖
        v := find(save(storage, alice.age, 42), alice.age) } φ }
    ~[findOnSave]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ v := 42 } φ } := by
  sol_chain
#last_line localValueDeclInitDrop

/-- `Account storage acc;`: nothing is left. -/
def storageLocalDeclSkip :
    dl![m]{ ⟨[ Account storage acc; ]⟩ φ }
    ~*> dl![m]{ φ } := by
  sol_chain
#last_line storageLocalDeclSkip

/-- `uint v;`: `v` is the default. -/
def valueDeclSkip :
    dl![m]{ ⟨[ uint v; ]⟩ φ }
    ~*> dl![m]{ { v := 0 } φ } := by
  sol_chain
#last_line valueDeclSkip

/-- `p = bob;` with `p` bound to `alice`: the alias is rebound, the later binding wins. -/
theorem storageLocalRootRebind :
    dl![m]{ { p := alice } ⟨[ p = bob; ]⟩ φ }
    ~*> dl![m]{ { p := alice } { p := bob } φ }
    ~[sequentialToParallel]~> dl![m]{ { p := alice ‖ p := bob } φ } := by
  sol_chain
#last_line storageLocalRootRebind

/-! ### Field and root reads -/

/-- `v = alice.account.balance;` from a storage where it is 10. -/
theorem storageFieldRead_unfold_rightFst :
    dl![m]{ { storage := save(storage, alice.account.balance, 10) } ⟨[ v = alice.account.balance; ]⟩ φ }
    ~[storageFieldRead_unfold_rightFst]~> dl![m]{ { storage := save(storage, alice.account.balance, 10) }
        ⟨[ Account storage sp1 = alice.account; v = sp1.balance; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.account.balance, 10) } { sp1 := alice.account }
        ⟨[ v = sp1.balance; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.account.balance, 10) } { sp1 := alice.account }
        { v := find(storage, sp1.balance) } φ }
    ~[sequentialToParallel]~> dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖ sp1 := alice.account ‖
        v := find(save(storage, alice.account.balance, 10), alice.account.balance) } φ }
    ~[findOnSave]~> dl![m]{
        { storage := save(storage, alice.account.balance, 10) ‖ sp1 := alice.account ‖ v := 10 } φ } := by
  sol_chain
#last_line storageFieldRead_unfold_rightFst

/-- `acc = bob.account;` with `acc` bound to `alice.account`. -/
theorem storageFieldReadBindLocalRoot :
    dl![m]{ { acc := alice.account } ⟨[ acc = bob.account; ]⟩ φ }
    ~*> dl![m]{ { acc := alice.account } { acc := bob.account } φ }
    ~[sequentialToParallel]~> dl![m]{ { acc := alice.account ‖ acc := bob.account } φ } := by
  sol_chain
#last_line storageFieldReadBindLocalRoot

/-- `account = bob.account;`: a struct read, which has no literal. -/
def storageFieldReadStoreRoot :
    dl![m]{ ⟨[ account = bob.account; ]⟩ φ }
    ~*> dl![m]{ { storage := store(storage, account, find(storage, bob.account)) } φ } := by
  sol_chain
#last_line storageFieldReadStoreRoot

/-- `v = alice.age;` from a storage where it is 42. -/
theorem storageFieldReadFind :
    dl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ v = alice.age; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, 42) } { v := find(storage, alice.age) } φ }
    ~[sequentialToParallel]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖
        v := find(save(storage, alice.age, 42), alice.age) } φ }
    ~[findOnSave]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ v := 42 } φ } := by
  sol_chain
#last_line storageFieldReadFind

/-- `v = total;` from a storage where it is 7. -/
theorem storageRootReadSelect :
    dl![m]{ { storage := store(storage, total, 7) } ⟨[ v = total; ]⟩ φ }
    ~*> dl![m]{ { storage := store(storage, total, 7) } { v := select(storage, total) } φ }
    ~[sequentialToParallel]~> dl![m]{ { storage := store(storage, total, 7) ‖
        v := select(store(storage, total, 7), total) } φ }
    ~[findOnSave]~> dl![m]{ { storage := store(storage, total, 7) ‖ v := 7 } φ } := by
  sol_chain
#last_line storageRootReadSelect

/-! ### `delete` -/

/-- `delete alice.account.token;` -/
theorem storageFieldDelete_unfold_leftFst :
    dl![m]{ ⟨[ delete alice.account.token; ]⟩ φ }
    ~[storageFieldDelete_unfold_leftFst]~> dl![m]{ ⟨[ Account storage sp1 = alice.account; delete sp1.token; ]⟩ φ }
    ~*> dl![m]{ { sp1 := alice.account } ⟨[ delete sp1.token; ]⟩ φ }
    ~*> dl![m]{ { sp1 := alice.account } { storage := delAt(storage, sp1.token) } φ }
    ~[sequentialToParallel]~> dl![m]{ { sp1 := alice.account ‖ storage := delAt(storage, alice.account.token) } φ } := by
  sol_chain
#last_line storageFieldDelete_unfold_leftFst

-- `bucket.tokens` for `alice.account.tokens`.
/-- `delete bucket.tokens[i];` with `i` 2. -/
theorem storageIndexDelete_unfold_leftFst :
    dl![m]{ { i := 2 } ⟨[ delete bucket.tokens[i]; ]⟩ φ }
    ~[storageIndexDelete_unfold_leftFst]~>
      dl![m]{ { i := 2 } ⟨[ Token[] storage sp1 = bucket.tokens; delete sp1[i]; ]⟩ φ }
    ~*> dl![m]{ { i := 2 } { sp1 := bucket.tokens } ⟨[ delete sp1[i]; ]⟩ φ }
    ~*> dl![m]{ { i := 2 } { sp1 := bucket.tokens } { storage := delAt(storage, sp1[i]) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { i := 2 ‖ sp1 := bucket.tokens ‖ storage := delAt(storage, bucket.tokens[2]) } φ } := by
  sol_chain
#last_line storageIndexDelete_unfold_leftFst

/-- `delete alice;` -/
def storageRootDelete :
    dl![m]{ ⟨[ delete alice; ]⟩ φ }
    ~*> dl![m]{ { storage := delAt(storage, alice) } φ } := by
  sol_chain
#last_line storageRootDelete

/-- `delete alice.account;` -/
def storageFieldDelete :
    dl![m]{ ⟨[ delete alice.account; ]⟩ φ }
    ~*> dl![m]{ { storage := delAt(storage, alice.account) } φ } := by
  sol_chain
#last_line storageFieldDelete

/-- `delete tokenById[id];` with `id` 3. -/
theorem storageIndexDelete :
    dl![m]{ { id := 3 } ⟨[ delete tokenById[id]; ]⟩ φ }
    ~*> dl![m]{ { id := 3 } { storage := delAt(storage, tokenById[id]) } φ }
    ~[sequentialToParallel]~> dl![m]{ { id := 3 ‖ storage := delAt(storage, tokenById[3]) } φ } := by
  sol_chain
#last_line storageIndexDelete

/-- `delete tokens[i];` with `i` 2. -/
theorem storageIndexArrayDelete :
    dl![m]{ { i := 2 } ⟨[ delete tokens[i]; ]⟩ φ }
    ~*> dl![m]{ { i := 2 } { storage := delAt(storage, tokens[i]) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ storage := delAt(storage, tokens[2]) } φ } := by
  sol_chain
#last_line storageIndexArrayDelete

/-! ### Writes through a receiver or an index that is not simple -/

-- `basket.items[i] = tokVal;` stands for `alice.account.tokens[i] = tokVal;`.
/-- `basket.items[i] = tokVal;` with `tokVal` 7 and `i` 2. -/
theorem storageIndexWriteCaptureAllComplexRecv :
    dl![m]{ { tokVal := 7 ‖ i := 2 } ⟨[ basket.items[i] = tokVal; ]⟩ φ }
    ~[storageIndexWriteCaptureAllComplexRecv]~> dl![m]{ { tokVal := 7 ‖ i := 2 }
        ⟨[ uint se1 = tokVal; uint[] storage sp1 = basket.items; uint ie1 = i; sp1[ie1] = se1; ]⟩ φ }
    ~*> dl![m]{ { tokVal := 7 ‖ i := 2 } { se1 := tokVal } { sp1 := basket.items } { ie1 := i }
        ⟨[ sp1[ie1] = se1; ]⟩ φ }
    ~*> dl![m]{ { tokVal := 7 ‖ i := 2 } { se1 := tokVal } { sp1 := basket.items } { ie1 := i }
        { storage := save(storage, sp1[ie1], se1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { tokVal := 7 ‖ i := 2 ‖ se1 := 7 ‖ sp1 := basket.items ‖ ie1 := 2 ‖ storage := save(storage, basket.items[2], 7) }
          φ } := by
  sol_chain
#last_line storageIndexWriteCaptureAllComplexRecv

/-- `alice.account.token = tokRef;` with `tokRef` bound to `bob.account.token`. -/
theorem storageFieldWriteStorageRef_unfold_leftFst :
    dl![m]{ { tokRef := bob.account.token } ⟨[ alice.account.token = tokRef; ]⟩ φ }
    ~[storageFieldWriteStorageRef_unfold_leftFst]~> dl![m]{ { tokRef := bob.account.token }
        ⟨[ Account storage sp1 = alice.account; sp1.token = tokRef; ]⟩ φ }
    ~*> dl![m]{ { tokRef := bob.account.token } { sp1 := alice.account } ⟨[ sp1.token = tokRef; ]⟩ φ }
    ~*> dl![m]{ { tokRef := bob.account.token } { sp1 := alice.account }
        { storage := save(storage, sp1.token, find(storage, tokRef)) } φ }
    ~[sequentialToParallel]~> dl![m]{ { tokRef := bob.account.token ‖ sp1 := alice.account ‖
        storage := save(storage, alice.account.token, find(storage, bob.account.token)) } φ } := by
  sol_chain
#last_line storageFieldWriteStorageRef_unfold_leftFst

-- `bucket.tokens` for `alice.account.tokens`.
/-- `bucket.tokens[i] = tokRef;` with `i` 2 and `tokRef` bound to `bob.account.token`. -/
theorem storageIndexWriteStorageRefCaptureAllComplexRecv :
    dl![m]{ { i := 2 ‖ tokRef := bob.account.token } ⟨[ bucket.tokens[i] = tokRef; ]⟩ φ }
    ~[storageIndexWriteStorageRefCaptureAllComplexRecv]~> dl![m]{ { i := 2 ‖ tokRef := bob.account.token }
        ⟨[ Token[] storage sp1 = bucket.tokens; uint ie1 = i; sp1[ie1] = tokRef; ]⟩ φ }
    ~*> dl![m]{ { i := 2 ‖ tokRef := bob.account.token } { sp1 := bucket.tokens } { ie1 := i }
        ⟨[ sp1[ie1] = tokRef; ]⟩ φ }
    ~*> dl![m]{ { i := 2 ‖ tokRef := bob.account.token } { sp1 := bucket.tokens } { ie1 := i }
        { storage := save(storage, sp1[ie1], find(storage, tokRef)) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ tokRef := bob.account.token ‖ sp1 := bucket.tokens ‖ ie1 := 2 ‖
        storage := save(storage, bucket.tokens[2], find(storage, bob.account.token)) } φ } := by
  sol_chain
#last_line storageIndexWriteStorageRefCaptureAllComplexRecv

-- The `++i` is the elaborator's: captured before the statement.
example : dl!{ ⟨ values[++i] = val; ⟩ true }
    = dl!{ ⟨ uint se1 = val; uint se2; se2 = ++i; values[se2] = se1; ⟩ true } := rfl

/-- `values[++i] = val;` with `i` 2 and `val` 7: the captures, the increment, the write at `3`. -/
theorem storageIndexWriteCaptureAllNonSimpleIndex :
    dl![m]{ { i := 2 ‖ val := 7 } ⟨[ values[++i] = val; ]⟩ φ }
    ~*> dl![m]{ { i := 2 ‖ val := 7 } { se1 := val } { se2 := 0 } ⟨[ se2 = ++i; values[se2] = se1; ]⟩ φ }
    ~[localAssignIncrement]~> dl![m]{ { i := 2 ‖ val := 7 } { se1 := val } { se2 := 0 } { i := i + 1 ‖ se2 := i + 1 }
        ⟨[ values[se2] = se1; ]⟩ φ }
    ~*> dl![m]{ { i := 2 ‖ val := 7 } { se1 := val } { se2 := 0 } { i := i + 1 ‖ se2 := i + 1 }
        { storage := save(storage, values[se2], se1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ val := 7 ‖ se1 := 7 ‖ se2 := 0 ‖ i := 2 + 1 ‖ se2 := 2 + 1 ‖ storage := save(storage, values[2 + 1], 7) }
          φ }
    ~[add_literals]~> dl![m]{
        { i := 2 ‖ val := 7 ‖ se1 := 7 ‖ se2 := 0 ‖ i := 3 ‖ se2 := 3 ‖ storage := save(storage, values[3], 7) } φ } := by
  sol_chain
#last_line storageIndexWriteCaptureAllNonSimpleIndex

example : dl!{ ⟨ tokens[++i] = tokRef; ⟩ true where Token storage tokRef }
    = dl!{ ⟨ uint se1; se1 = ++i; tokens[se1] = tokRef; ⟩ true where Token storage tokRef } := rfl

/-- `tokens[++i] = tokRef;` with `i` 2 and `tokRef` bound to `bob.account.token`. -/
theorem storageIndexWriteStorageRefCaptureAllNonSimpleIndex :
    dl![m]{ { i := 2 ‖ tokRef := bob.account.token } ⟨[ tokens[++i] = tokRef; ]⟩ φ }
    ~[valueDeclSkip]~> dl![m]{ { i := 2 ‖ tokRef := bob.account.token } { se1 := 0 }
        ⟨[ se1 = ++i; tokens[se1] = tokRef; ]⟩ φ }
    ~[localAssignIncrement]~> dl![m]{ { i := 2 ‖ tokRef := bob.account.token } { se1 := 0 }
        { i := i + 1 ‖ se1 := i + 1 } ⟨[ tokens[se1] = tokRef; ]⟩ φ }
    ~*> dl![m]{ { i := 2 ‖ tokRef := bob.account.token } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 }
        { storage := save(storage, tokens[se1], find(storage, tokRef)) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ tokRef := bob.account.token ‖ se1 := 0 ‖ i := 2 + 1 ‖ se1 := 2 + 1 ‖
        storage := save(storage, tokens[2 + 1], find(storage, bob.account.token)) } φ }
    ~[add_literals]~> dl![m]{ { i := 2 ‖ tokRef := bob.account.token ‖ se1 := 0 ‖ i := 3 ‖ se1 := 3 ‖
        storage := save(storage, tokens[3], find(storage, bob.account.token)) } φ } := by
  sol_chain
#last_line storageIndexWriteStorageRefCaptureAllNonSimpleIndex

/-! ### Writes with a source that is not simple -/

/-- `alice.age = ageVal + 1;` with `ageVal` 42: the source captured, the sum folded to 43. -/
theorem fieldWriteValueRhsCapture :
    dl![m]{ { ageVal := 42 } ⟨[ alice.age = ageVal + 1; ]⟩ φ }
    ~[fieldWriteValueRhsCapture]~> dl![m]{ { ageVal := 42 } ⟨[ uint se1 = ageVal + 1; alice.age = se1; ]⟩ φ }
    ~*> dl![m]{ { ageVal := 42 } { se1 := ageVal + 1 } ⟨[ alice.age = se1; ]⟩ φ }
    ~*> dl![m]{ { ageVal := 42 } { se1 := ageVal + 1 } { storage := save(storage, alice.age, se1) } φ }
    ~[sequentialToParallel]~> dl![m]{ { ageVal := 42 ‖ se1 := 42 + 1 ‖ storage := save(storage, alice.age, 42 + 1) } φ }
    ~[add_literals]~> dl![m]{ { ageVal := 42 ‖ se1 := 43 ‖ storage := save(storage, alice.age, 43) } φ } := by
  sol_chain
#last_line fieldWriteValueRhsCapture

-- The call is the elaborator's.
example : dl!{ ⟨ values[i] = makeValue(); ⟩ true }
    = dl!{ ⟨ uint se1; se1 = makeValue(); values[i] = se1; ⟩ true } := rfl

/-- `values[i] = makeValue();` with `i` 2, from a storage where `total` is 7: the call's body inlined
(`functionBodyExpand`), its result written. -/
theorem indexWriteValueRhsCapture :
    dl![m]{ { i := 2 ‖ storage := store(storage, total, 7) } ⟨[ values[i] = makeValue(); ]⟩ φ }
    ~[valueDeclSkip]~> dl![m]{ { i := 2 ‖ storage := store(storage, total, 7) } { se1 := 0 }
        ⟨[ se1 = makeValue(); values[i] = se1; ]⟩ φ }
    ~[functionBodyExpand]~> dl![m]{ { i := 2 ‖ storage := store(storage, total, 7) } { se1 := 0 }
        ⟨[ uint se2; se2 = total; se1 = se2; values[i] = se1; ]⟩ φ }
    ~*> dl![m]{ { i := 2 ‖ storage := store(storage, total, 7) } { se1 := 0 } { se2 := 0 }
        { se2 := select(storage, total) } { se1 := se2 } ⟨[ values[i] = se1; ]⟩ φ }
    ~*> dl![m]{ { i := 2 ‖ storage := store(storage, total, 7) } { se1 := 0 } { se2 := 0 }
        { se2 := select(storage, total) } { se1 := se2 } { storage := save(storage, values[i], se1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ se1 := 0 ‖ se2 := 0 ‖ se2 := select(store(storage, total, 7), total) ‖
            se1 := select(store(storage, total, 7), total) ‖
            storage :=
              save(store(storage, total, 7), values[2]@store(storage, total, 7), select(store(storage, total, 7), total)) }
          φ }
    ~[findOnSave]~> dl![m]{
        { i := 2 ‖ se1 := 0 ‖ se2 := 0 ‖ se2 := 7 ‖ se1 := 7 ‖
            storage := save(store(storage, total, 7), values[2]@store(storage, total, 7), 7) }
          φ } := by
  sol_chain
#last_line indexWriteValueRhsCapture

example : dl!{ ⟨ total = makeValue(); ⟩ true }
    = dl!{ ⟨ uint se1; se1 = makeValue(); total = se1; ⟩ true } := rfl

/-- `total = makeValue();` from a storage where `total` is 7. -/
theorem storageRootWriteValueRhsCapture :
    dl![m]{ { storage := store(storage, total, 7) } ⟨[ total = makeValue(); ]⟩ φ }
    ~[valueDeclSkip]~> dl![m]{ { storage := store(storage, total, 7) } { se1 := 0 }
        ⟨[ se1 = makeValue(); total = se1; ]⟩ φ }
    ~[functionBodyExpand]~> dl![m]{ { storage := store(storage, total, 7) } { se1 := 0 }
        ⟨[ uint se2; se2 = total; se1 = se2; total = se1; ]⟩ φ }
    ~*> dl![m]{ { storage := store(storage, total, 7) } { se1 := 0 } { se2 := 0 } { se2 := select(storage, total) }
        { se1 := se2 } ⟨[ total = se1; ]⟩ φ }
    ~*> dl![m]{ { storage := store(storage, total, 7) } { se1 := 0 } { se2 := 0 } { se2 := select(storage, total) }
        { se1 := se2 } { storage := store(storage, total, se1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { se1 := 0 ‖ se2 := 0 ‖ se2 := select(store(storage, total, 7), total) ‖
            se1 := select(store(storage, total, 7), total) ‖
            storage := store(store(storage, total, 7), total, select(store(storage, total, 7), total)) }
          φ }
    ~[findOnSave]~> dl![m]{
        { se1 := 0 ‖ se2 := 0 ‖ se2 := 7 ‖ se1 := 7 ‖ storage := store(store(storage, total, 7), total, 7) } φ } := by
  sol_chain
#last_line storageRootWriteValueRhsCapture

-- Lean's `storageFieldRead_unfold_rightSndResult`.
/-- `alice.account = bob.account;`: the source aliased (`sp1`), then copied; a struct read, which has no
literal. -/
theorem storageFieldWriteCaptureSrc :
    dl![m]{ ⟨[ alice.account = bob.account; ]⟩ φ }
    ~[storageFieldRead_unfold_rightSndResult]~>
      dl![m]{ ⟨[ Account storage sp1 = bob.account; alice.account = sp1; ]⟩ φ }
    ~*> dl![m]{ { sp1 := bob.account } ⟨[ alice.account = sp1; ]⟩ φ }
    ~*> dl![m]{ { sp1 := bob.account } { storage := save(storage, alice.account, find(storage, sp1)) } φ }
    ~[sequentialToParallel]~> dl![m]{ { sp1 := bob.account ‖
        storage := save(storage, alice.account, find(storage, bob.account)) } φ } := by
  sol_chain
#last_line storageFieldWriteCaptureSrc

-- Lean's `storageFieldRead_unfold_rightFst`: the receiver `bob.account` is unfolded first.
/-- `tokens[i] = bob.account.token;` with `i` 2: two aliases, then the copy. -/
theorem storageIndexWriteStorageRefRhsCapture :
    dl![m]{ { i := 2 } ⟨[ tokens[i] = bob.account.token; ]⟩ φ }
    ~[storageFieldRead_unfold_rightFst]~>
      dl![m]{ { i := 2 } ⟨[ Account storage sp1 = bob.account; tokens[i] = sp1.token; ]⟩ φ }
    ~*> dl![m]{ { i := 2 } { sp1 := bob.account } ⟨[ tokens[i] = sp1.token; ]⟩ φ }
    ~[storageFieldRead_unfold_rightSndResult]~>
      dl![m]{ { i := 2 } { sp1 := bob.account } ⟨[ Token storage sp2 = sp1.token; tokens[i] = sp2; ]⟩ φ }
    ~*> dl![m]{ { i := 2 } { sp1 := bob.account } { sp2 := sp1.token } ⟨[ tokens[i] = sp2; ]⟩ φ }
    ~*> dl![m]{ { i := 2 } { sp1 := bob.account } { sp2 := sp1.token }
        { storage := save(storage, tokens[i], find(storage, sp2)) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ sp1 := bob.account ‖ sp2 := bob.account.token ‖
        storage := save(storage, tokens[2], find(storage, bob.account.token)) } φ } := by
  sol_chain
#last_line storageIndexWriteStorageRefRhsCapture

/-! ### A write at an index: copy or save -/

/-- `tokens[i] = tokRef;` with `i` 2 and `tokRef` bound to `bob.account.token`. -/
theorem storageIndexWriteArrayCopySource :
    dl![m]{ { i := 2 ‖ tokRef := bob.account.token } ⟨[ tokens[i] = tokRef; ]⟩ φ }
    ~*> dl![m]{ { i := 2 ‖ tokRef := bob.account.token }
        { storage := save(storage, tokens[i], find(storage, tokRef)) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ tokRef := bob.account.token ‖
        storage := save(storage, tokens[2], find(storage, bob.account.token)) } φ } := by
  sol_chain
#last_line storageIndexWriteArrayCopySource

/-- `tokenById[id] = tokRef;` with `id` 3 and `tokRef` bound to `bob.account.token`. -/
theorem storageIndexWriteMappingCopySource :
    dl![m]{ { id := 3 ‖ tokRef := bob.account.token } ⟨[ tokenById[id] = tokRef; ]⟩ φ }
    ~*> dl![m]{ { id := 3 ‖ tokRef := bob.account.token }
        { storage := save(storage, tokenById[id], find(storage, tokRef)) } φ }
    ~[sequentialToParallel]~> dl![m]{ { id := 3 ‖ tokRef := bob.account.token ‖
        storage := save(storage, tokenById[3], find(storage, bob.account.token)) } φ } := by
  sol_chain
#last_line storageIndexWriteMappingCopySource

-- `values[i] = tokVal;` stands for `tokens[i] = tokVal;`.
/-- `values[i] = tokVal;` with `i` 2 and `tokVal` 7. -/
theorem storageIndexWriteArraySave :
    dl![m]{ { i := 2 ‖ tokVal := 7 } ⟨[ values[i] = tokVal; ]⟩ φ }
    ~*> dl![m]{ { i := 2 ‖ tokVal := 7 } { storage := save(storage, values[i], tokVal) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ tokVal := 7 ‖ storage := save(storage, values[2], 7) } φ } := by
  sol_chain
#last_line storageIndexWriteArraySave

/-- `balances[addr] = amount;` with `addr` 3 and `amount` 10. -/
theorem storageIndexWriteMappingSave :
    dl![m]{ { addr := 3 ‖ amount := 10 } ⟨[ balances[addr] = amount; ]⟩ φ }
    ~*> dl![m]{ { addr := 3 ‖ amount := 10 } { storage := save(storage, balances[addr], amount) } φ }
    ~[sequentialToParallel]~> dl![m]{ { addr := 3 ‖ amount := 10 ‖ storage := save(storage, balances[3], 10) } φ } := by
  sol_chain
#last_line storageIndexWriteMappingSave

/-! ### Reads at an index -/

-- `bucket.tokens` for `alice.account.tokens`.
/-- `tok = bucket.tokens[i];` with `i` 2. -/
theorem storageIndexRead_unfold_rightFst :
    dl![m]{ { i := 2 } ⟨[ tok = bucket.tokens[i]; ]⟩ φ where Token storage tok }
    ~[storageIndexRead_unfold_rightFst]~>
      dl![m]{ { i := 2 } ⟨[ Token[] storage sp1 = bucket.tokens; tok = sp1[i]; ]⟩ φ where Token storage tok }
    ~*> dl![m]{ { i := 2 } { sp1 := bucket.tokens } { tok := sp1[i] } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ sp1 := bucket.tokens ‖ tok := bucket.tokens[2] } φ } := by
  sol_chain
#last_line storageIndexRead_unfold_rightFst

example : dl!{ ⟨ tok = tokens[++i]; ⟩ true where Token storage tok }
    = dl!{ ⟨ uint se1; se1 = ++i; tok = tokens[se1]; ⟩ true where Token storage tok } := rfl

/-- `tok = tokens[++i];` with `i` 2: `tok` bound to `tokens[3]`. -/
theorem storageIndexRead_unfold_rightSndIndex :
    dl![m]{ { i := 2 } ⟨[ tok = tokens[++i]; ]⟩ φ where Token storage tok }
    ~[valueDeclSkip]~> dl![m]{ { i := 2 } { se1 := 0 } ⟨[ se1 = ++i; tok = tokens[se1]; ]⟩ φ where Token storage tok }
    ~[localAssignIncrement]~> dl![m]{ { i := 2 } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 }
        ⟨[ tok = tokens[se1]; ]⟩ φ where Token storage tok }
    ~*> dl![m]{ { i := 2 } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 } { tok := tokens[se1] } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ se1 := 0 ‖ i := 2 + 1 ‖ se1 := 2 + 1 ‖ tok := tokens[2 + 1] } φ }
    ~[add_literals]~> dl![m]{ { i := 2 ‖ se1 := 0 ‖ i := 3 ‖ se1 := 3 ‖ tok := tokens[3] } φ } := by
  sol_chain
#last_line storageIndexRead_unfold_rightSndIndex

/-- `tok = tokens[i];` with `i` 2. -/
theorem storageIndexReadArrayBindLocalRoot :
    dl![m]{ { i := 2 } ⟨[ tok = tokens[i]; ]⟩ φ where Token storage tok }
    ~*> dl![m]{ { i := 2 } { tok := tokens[i] } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ tok := tokens[2] } φ } := by
  sol_chain
#last_line storageIndexReadArrayBindLocalRoot

/-- `led = ledgers[i];` with `i` 2. -/
theorem storageIndexReadArrayBindLocalRootMappingElement :
    dl![m]{ { i := 2 } ⟨[ led = ledgers[i]; ]⟩ φ where mapping(uint => uint) storage led }
    ~*> dl![m]{ { i := 2 } { led := ledgers[i] } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 2 ‖ led := ledgers[2] } φ } := by
  sol_chain
#last_line storageIndexReadArrayBindLocalRootMappingElement

/-- `tok = tokenById[id];` with `id` 3. -/
theorem storageIndexReadMappingBindLocalRoot :
    dl![m]{ { id := 3 } ⟨[ tok = tokenById[id]; ]⟩ φ where Token storage tok }
    ~*> dl![m]{ { id := 3 } { tok := tokenById[id] } φ }
    ~[sequentialToParallel]~> dl![m]{ { id := 3 ‖ tok := tokenById[3] } φ } := by
  sol_chain
#last_line storageIndexReadMappingBindLocalRoot

/-- `alice = people[i];` with `i` 2: a struct read, which has no literal. -/
theorem storageIndexReadArrayStoreRoot :
    dl![m]{ { i := 2 } ⟨[ alice = people[i]; ]⟩ φ }
    ~*> dl![m]{ { i := 2 } { storage := store(storage, alice, find(storage, people[i])) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { i := 2 ‖ storage := store(storage, alice, find(storage, people[2])) } φ } := by
  sol_chain
#last_line storageIndexReadArrayStoreRoot

/-- `alice = personById[id];` with `id` 3: a struct read, which has no literal. -/
theorem storageIndexReadMappingStoreRoot :
    dl![m]{ { id := 3 } ⟨[ alice = personById[id]; ]⟩ φ }
    ~*> dl![m]{ { id := 3 } { storage := store(storage, alice, find(storage, personById[id])) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { id := 3 ‖ storage := store(storage, alice, find(storage, personById[3])) } φ } := by
  sol_chain
#last_line storageIndexReadMappingStoreRoot

/-- `v = values[i];` with `i` 2, from a storage where `values[2]` is 7, under the box: the read checks the
index in the state it runs in (`values[2]@S`), which `findOnSave` reads past only there. -/
theorem storageIndexReadArrayFind :
    dl![.box]{ { i := 2 ‖ storage := save(storage, values[2], 7) } ⟨[ v = values[i]; ]⟩ φ }
    ~*> dl![.box]{ { i := 2 ‖ storage := save(storage, values[2], 7) }
        { v := find(storage, values[i]) } φ }
    ~[sequentialToParallel]~> dl![.box]{ { i := 2 ‖ storage := save(storage, values[2], 7) ‖
        v := find(save(storage, values[2], 7), values[2]@save(storage, values[2], 7)) } φ }
    ~[findOnSave]~> dl![.box]{ { i := 2 ‖ storage := save(storage, values[2], 7) ‖ v := 7 } φ } := by
  sol_chain
#last_line storageIndexReadArrayFind

/-- `v = balances[addr];` with `addr` 3, from a storage where `balances[3]` is 10, under the box, as
`storageIndexReadArrayFind`. -/
theorem storageIndexReadMappingFind :
    dl![.box]{ { addr := 3 ‖ storage := save(storage, balances[3], 10) } ⟨[ v = balances[addr]; ]⟩ φ }
    ~*> dl![.box]{ { addr := 3 ‖ storage := save(storage, balances[3], 10) }
        { v := find(storage, balances[addr]) } φ }
    ~[sequentialToParallel]~> dl![.box]{ { addr := 3 ‖ storage := save(storage, balances[3], 10) ‖
        v := find(save(storage, balances[3], 10), balances[3]@save(storage, balances[3], 10)) } φ }
    ~[findOnSave]~> dl![.box]{ { addr := 3 ‖ storage := save(storage, balances[3], 10) ‖ v := 10 } φ } := by
  sol_chain
#last_line storageIndexReadMappingFind

/-! ### `push` -/

-- `bucket.tokens` for `alice.account.tokens`.
/-- `bucket.tokens.push(tok);` with `tok` bound to `bob.account.token`. -/
theorem storagePushValue_unfold_leftFstReceiver :
    dl![m]{ { tok := bob.account.token } ⟨[ bucket.tokens.push(tok); ]⟩ φ }
    ~[storagePushValue_unfold_leftFstReceiver]~>
      dl![m]{ { tok := bob.account.token } ⟨[ Token[] storage sp1 = bucket.tokens; sp1.push(tok); ]⟩ φ }
    ~*> dl![m]{ { tok := bob.account.token } { sp1 := bucket.tokens } ⟨[ sp1.push(tok); ]⟩ φ }
    ~*> dl![m]{ { tok := bob.account.token } { sp1 := bucket.tokens }
        { storage := save(save(storage, sp1[sp1.length], find(storage, tok)), sp1.length, sp1.length + 1) } φ }
    ~[sequentialToParallel]~> dl![m]{ { tok := bob.account.token ‖ sp1 := bucket.tokens ‖
        storage := save(save(storage, bucket.tokens[bucket.tokens.length], find(storage, bob.account.token)),
          bucket.tokens.length, bucket.tokens.length + 1) } φ } := by
  sol_chain
#last_line storagePushValue_unfold_leftFstReceiver

example : dl!{ ⟨ values.push(makeValue()); ⟩ true }
    = dl!{ ⟨ uint se1; se1 = makeValue(); values.push(se1); ⟩ true } := rfl

/-- `values.push(makeValue());` from a storage where `total` is 7. -/
theorem storagePushValue_unfold_rightSndArgument :
    dl![m]{ { storage := store(storage, total, 7) } ⟨[ values.push(makeValue()); ]⟩ φ }
    ~[valueDeclSkip]~> dl![m]{ { storage := store(storage, total, 7) } { se1 := 0 }
        ⟨[ se1 = makeValue(); values.push(se1); ]⟩ φ }
    ~[functionBodyExpand]~> dl![m]{ { storage := store(storage, total, 7) } { se1 := 0 }
        ⟨[ uint se2; se2 = total; se1 = se2; values.push(se1); ]⟩ φ }
    ~*> dl![m]{ { storage := store(storage, total, 7) } { se1 := 0 } { se2 := 0 } { se2 := select(storage, total) }
        { se1 := se2 } ⟨[ values.push(se1); ]⟩ φ }
    ~*> dl![m]{ { storage := store(storage, total, 7) } { se1 := 0 } { se2 := 0 } { se2 := select(storage, total) }
        { se1 := se2 } { storage := save(save(storage, values[values.length], se1), values.length, values.length + 1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { se1 := 0 ‖ se2 := 0 ‖ se2 := select(store(storage, total, 7), total) ‖
            se1 := select(store(storage, total, 7), total) ‖
            storage :=
              save(save(store(storage, total, 7), values[values.length], select(store(storage, total, 7), total)),
                values.length, values.length + 1) }
          φ }
    ~[findOnSave]~> dl![m]{
        { se1 := 0 ‖ se2 := 0 ‖ se2 := 7 ‖ se1 := 7 ‖
            storage := save(save(store(storage, total, 7), values[values.length], 7), values.length, values.length + 1) }
          φ } := by
  sol_chain
#last_line storagePushValue_unfold_rightSndArgument

/-- `tokens.push(tokRef);` with `tokRef` bound to `bob.account.token`. -/
theorem storagePushValueCopySource :
    dl![m]{ { tokRef := bob.account.token } ⟨[ tokens.push(tokRef); ]⟩ φ }
    ~*> dl![m]{ { tokRef := bob.account.token }
        { storage := save(save(storage, tokens[tokens.length], find(storage, tokRef)), tokens.length,
          tokens.length + 1) } φ }
    ~[sequentialToParallel]~> dl![m]{ { tokRef := bob.account.token ‖
        storage := save(save(storage, tokens[tokens.length], find(storage, bob.account.token)), tokens.length,
          tokens.length + 1) } φ } := by
  sol_chain
#last_line storagePushValueCopySource

/-- `values.push(valueVal);` with `valueVal` 7. -/
theorem storagePushValueSave :
    dl![m]{ { valueVal := 7 } ⟨[ values.push(valueVal); ]⟩ φ }
    ~*> dl![m]{ { valueVal := 7 }
        { storage := save(save(storage, values[values.length], valueVal), values.length, values.length + 1) } φ }
    ~[sequentialToParallel]~> dl![m]{ { valueVal := 7 ‖
        storage := save(save(storage, values[values.length], 7), values.length, values.length + 1) } φ } := by
  sol_chain
#last_line storagePushValueSave

/-- `bucket.tokens.push();` -/
theorem storagePush_unfold_leftFstReceiver :
    dl![m]{ ⟨[ bucket.tokens.push(); ]⟩ φ }
    ~[storagePush_unfold_leftFstReceiver]~> dl![m]{ ⟨[ Token[] storage sp1 = bucket.tokens; sp1.push(); ]⟩ φ }
    ~*> dl![m]{ { sp1 := bucket.tokens } ⟨[ sp1.push(); ]⟩ φ }
    ~*> dl![m]{ { sp1 := bucket.tokens } { storage := save(storage, sp1.length, sp1.length + 1) } φ }
    ~[sequentialToParallel]~> dl![m]{ { sp1 := bucket.tokens ‖
        storage := save(storage, bucket.tokens.length, bucket.tokens.length + 1) } φ } := by
  sol_chain
#last_line storagePush_unfold_leftFstReceiver

/-- `values.push();` -/
def storagePushLengthSave :
    dl![m]{ ⟨[ values.push(); ]⟩ φ }
    ~*> dl![m]{
        { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) } φ } := by
  sol_chain
#last_line storagePushLengthSave

/-- `tokens.push();` -/
def storagePushLengthSaveReferenceElement :
    dl![m]{ ⟨[ tokens.push(); ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) } φ } := by
  sol_chain
#last_line storagePushLengthSaveReferenceElement

/-! ### `push` bound to a local -/

/-- `sp = bucket.tokens.push();` -/
theorem storageLocalRootPush_unfold_leftFstReceiver :
    dl![m]{ ⟨[ sp = bucket.tokens.push(); ]⟩ φ where Token storage sp }
    ~[storageLocalRootPush_unfold_leftFstReceiver]~>
      dl![m]{ ⟨[ Token[] storage sp1 = bucket.tokens; sp = sp1.push(); ]⟩ φ where Token storage sp }
    ~*> dl![m]{ { sp1 := bucket.tokens } ⟨[ sp = sp1.push(); ]⟩ φ }
    ~*> dl![m]{ { sp1 := bucket.tokens } { storage := save(storage, sp1.length, sp1.length + 1) ‖ sp := sp1[sp1.length] } φ }
    ~[sequentialToParallel]~> dl![m]{ { sp1 := bucket.tokens ‖
        storage := save(storage, bucket.tokens.length, bucket.tokens.length + 1) ‖
        sp := bucket.tokens[bucket.tokens.length] } φ } := by
  sol_chain
#last_line storageLocalRootPush_unfold_leftFstReceiver

/-- `sp = tokens.push();` -/
def storageLocalRootPushBind :
    dl![m]{ ⟨[ sp = tokens.push(); ]⟩ φ where Token storage sp }
    ~*>
      dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] } φ } := by
  sol_chain
#last_line storageLocalRootPushBind

/-- `led = ledgers.push();` -/
def storageLocalRootPushBindMappingElement :
    dl![m]{ ⟨[ led = ledgers.push(); ]⟩ φ where mapping(uint => uint) storage led }
    ~*> dl![m]{
        { storage := save(storage, ledgers.length, ledgers.length + 1) ‖ led := ledgers[ledgers.length] } φ } := by
  sol_chain
#last_line storageLocalRootPushBindMappingElement

/-! ### `pop` -/

-- `bucket.tokens` for `alice.account.tokens`.
/-- `bucket.tokens.pop();` -/
theorem storagePop_unfold_leftFstReceiver :
    dl![m]{ ⟨[ bucket.tokens.pop(); ]⟩ φ }
    ~[storagePop_unfold_leftFstReceiver]~> dl![m]{ ⟨[ Token[] storage sp1 = bucket.tokens; sp1.pop(); ]⟩ φ }
    ~*> dl![m]{ { sp1 := bucket.tokens } ⟨[ sp1.pop(); ]⟩ φ }
    ~*> dl![m]{ { sp1 := bucket.tokens }
        { storage := save(delAt(storage, sp1[sp1.length - 1]), sp1.length, sp1.length - 1) } φ }
    ~[sequentialToParallel]~> dl![m]{ { sp1 := bucket.tokens ‖
        storage := save(delAt(storage, bucket.tokens[bucket.tokens.length - 1]), bucket.tokens.length,
          bucket.tokens.length - 1) } φ } := by
  sol_chain
#last_line storagePop_unfold_leftFstReceiver

/-- `tokens.pop();` -/
def storagePopSave :
    dl![m]{ ⟨[ tokens.pop(); ]⟩ φ }
    ~*> dl![m]{
        { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) } φ } := by
  sol_chain
#last_line storagePopSave

/-- `ledgers.pop();` -/
def storagePopSaveMappingElement :
    dl![m]{ ⟨[ ledgers.pop(); ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, ledgers.length, ledgers.length - 1) } φ } := by
  sol_chain
#last_line storagePopSaveMappingElement

/-! ### `require` and `assert`

Box chains: under `m` a chain stops at the failing branch's `revert();`.  Under the box it leaves `true`
(`revertBox`); the condition, once a literal, is read into the branches (`applyOnRigid` for an update of
locals, `applyOnPV` for one that also writes the storage), and folds them (`concrete`). -/

-- The call is the elaborator's; the capture rule itself fires on a condition
-- that is no simple expression, a state variable.
example : dl!{ ⟨ require(checkBalance()); ⟩ true }
    = dl!{ ⟨ bool se1; se1 = checkBalance(); require(se1); ⟩ true } := rfl

/-- `require(checkBalance());`: the call inlined, its `true` required. -/
theorem requireConditionCapture_call :
    dl![.box]{ ⟨[ require(checkBalance()); ]⟩ φ }
    ~[valueDeclSkip]~> dl![.box]{ { se1 := false } ⟨[ se1 = checkBalance(); require(se1); ]⟩ φ }
    ~[functionBodyExpand]~> dl![.box]{ { se1 := false } ⟨[ bool se2; se2 = true; se1 = se2; require(se1); ]⟩ φ }
    ~*> dl![.box]{ { se1 := false } { se2 := false } { se2 := true } { se1 := se2 } ⟨[ require(se1); ]⟩ φ }
    ~*> dl![.box]{ { se1 := false } { se2 := false } { se2 := true } { se1 := se2 }
        ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[revertBox]~> dl![.box]{ { se1 := false } { se2 := false } { se2 := true } { se1 := se2 }
        ((se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[sequentialToParallel]~> dl![.box]{ { se1 := false ‖ se2 := false ‖ se2 := true ‖ se1 := true }
        ((se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[applyOnRigid]~> dl![.box]{
        (true ≐ true → { se1 := false ‖ se2 := false ‖ se2 := true ‖ se1 := true } φ) ∧
          (true ≐ false → true) ∧
            ({ se1 := false ‖ se2 := false ‖ se2 := true ‖ se1 := true } ⟨[ revert(); ]⟩ false ∨ true ≐ true ∨
              true ≐ false) }
    ~[concrete]~> dl![.box]{ { se1 := false ‖ se2 := false ‖ se2 := true ‖ se1 := true } φ } := by
  sol_chain
#last_line requireConditionCapture_call

-- `where bool se1`: a local bound to a read (`se1 := select(storage, flag)`) reads as a `uint` without it,
-- though `#chain` prints the line without it.
/-- `require(flag);` from a storage where `flag` is `true`: the capture read off the starting storage
(`findOnSave`), the condition read into the goals (`applyOnPV`), and the goals folded. -/
theorem requireConditionCapture :
    dl![.box]{ { storage := store(storage, flag, true) } ⟨[ require(flag); ]⟩ φ }
    ~[requireConditionCapture]~>
      dl![.box]{ { storage := store(storage, flag, true) } ⟨[ bool se1 = flag; require(se1); ]⟩ φ }
    ~*> dl![.box]{ { storage := store(storage, flag, true) } { se1 := select(storage, flag) } ⟨[ require(se1); ]⟩ φ
        where bool se1 }
    ~*> dl![.box]{ { storage := store(storage, flag, true) } { se1 := select(storage, flag) }
        ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[revertBox]~> dl![.box]{ { storage := store(storage, flag, true) } { se1 := select(storage, flag) }
        ((se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[sequentialToParallel]~> dl![.box]{
        { storage := store(storage, flag, true) ‖ se1 := select(store(storage, flag, true), flag) }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → true) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[concrete]~> dl![.box]{
        { storage := store(storage, flag, true) ‖ se1 := select(store(storage, flag, true), flag) }
          ((se1 ≐ true → φ) ∧ ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[findOnSave]~> dl![.box]{
        { storage := store(storage, flag, true) ‖ se1 := true }
          ((se1 ≐ true → φ) ∧ ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[applyOnPV]~> dl![.box]{
        { storage := store(storage, flag, true) ‖ se1 := true }
          ((true ≐ true → φ) ∧ ([ revert(); ] false ∨ true ≐ true ∨ true ≐ false)) }
    ~[concrete]~> dl![.box]{ { storage := store(storage, flag, true) ‖ se1 := true } φ } := by
  sol_chain
#last_line requireConditionCapture

example : dl!{ ⟨ assert(checkInvariant()); ⟩ true }
    = dl!{ ⟨ bool se1; se1 = checkInvariant(); assert(se1); ⟩ true } := rfl

/-- `assert(checkInvariant());`: the call inlined, its `true` asserted.  An
`assert` checks rather than branches (`assertSimple`): no revert, so the chain
runs under any `m`. -/
theorem assertConditionCapture_call :
    dl![m]{ ⟨[ assert(checkInvariant()); ]⟩ φ }
    ~[valueDeclSkip]~> dl![m]{ { se1 := false } ⟨[ se1 = checkInvariant(); assert(se1); ]⟩ φ }
    ~[functionBodyExpand]~> dl![m]{ { se1 := false } ⟨[ bool se2; se2 = true; se1 = se2; assert(se1); ]⟩ φ }
    ~*> dl![m]{ { se1 := false } { se2 := false } { se2 := true } { se1 := se2 } ⟨[ assert(se1); ]⟩ φ }
    ~*> dl![m]{ { se1 := false } { se2 := false } { se2 := true } { se1 := se2 }
        ((se1 ≐ true → φ) ∧ se1 ≐ true) }
    ~[sequentialToParallel]~> dl![m]{ { se1 := false ‖ se2 := false ‖ se2 := true ‖ se1 := true }
        ((se1 ≐ true → φ) ∧ se1 ≐ true) }
    ~[applyOnRigid]~> dl![m]{
        (true ≐ true → { se1 := false ‖ se2 := false ‖ se2 := true ‖ se1 := true } φ) ∧ true ≐ true }
    ~[concrete]~> dl![m]{ { se1 := false ‖ se2 := false ‖ se2 := true ‖ se1 := true } φ } := by
  sol_chain
#last_line assertConditionCapture_call

/-- `assert(flag);` from a storage where `flag` is `true`: the condition owed and assumed, then folded. -/
theorem assertConditionCapture :
    dl![m]{ { storage := store(storage, flag, true) } ⟨[ assert(flag); ]⟩ φ }
    ~[assertConditionCapture]~>
      dl![m]{ { storage := store(storage, flag, true) } ⟨[ bool se1 = flag; assert(se1); ]⟩ φ }
    ~*> dl![m]{ { storage := store(storage, flag, true) } { se1 := select(storage, flag) } ⟨[ assert(se1); ]⟩ φ
        where bool se1 }
    ~*> dl![m]{ { storage := store(storage, flag, true) } { se1 := select(storage, flag) }
        ((se1 ≐ true → φ) ∧ se1 ≐ true) }
    ~[sequentialToParallel]~> dl![m]{
        { storage := store(storage, flag, true) ‖ se1 := select(store(storage, flag, true), flag) }
          ((se1 ≐ true → φ) ∧ se1 ≐ true) }
    ~[findOnSave]~> dl![m]{ { storage := store(storage, flag, true) ‖ se1 := true } ((se1 ≐ true → φ) ∧ se1 ≐ true) }
    ~[applyOnPV]~> dl![m]{ { storage := store(storage, flag, true) ‖ se1 := true } ((true ≐ true → φ) ∧ true ≐ true) }
    ~[concrete]~> dl![m]{ { storage := store(storage, flag, true) ‖ se1 := true } φ } := by
  sol_chain
#last_line assertConditionCapture

/-- `require(ok);` with `ok` `true`: the three goals, the failing one `true` under the box, and the condition
folded. -/
theorem requireSimple :
    dl![.box]{ { ok := true } ⟨[ require(ok); ]⟩ φ }
    ~*> dl![.box]{ { ok := true }
        ((ok ≐ true → φ) ∧ (ok ≐ false → ⟨[ revert(); ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ ok ≐ true ∨ ok ≐ false)) }
    ~[revertBox]~> dl![.box]{ { ok := true }
        ((ok ≐ true → φ) ∧ (ok ≐ false → true) ∧ (⟨[ revert(); ]⟩ false ∨ ok ≐ true ∨ ok ≐ false)) }
    ~[applyOnRigid]~> dl![.box]{
        (true ≐ true → { ok := true } φ) ∧
          (true ≐ false → true) ∧ ({ ok := true } ⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
    ~[concrete]~> dl![.box]{ { ok := true } φ } := by
  sol_chain
#last_line requireSimple

/-- `assert(ok);` with `ok` `true`: the two goals, the condition assumed and owed, folded. -/
theorem assertSimple :
    dl![m]{ { ok := true } ⟨[ assert(ok); ]⟩ φ }
    ~*> dl![m]{ { ok := true } ((ok ≐ true → φ) ∧ ok ≐ true) }
    ~[applyOnRigid]~> dl![m]{ (true ≐ true → { ok := true } φ) ∧ true ≐ true }
    ~[concrete]~> dl![m]{ { ok := true } φ } := by
  sol_chain
#last_line assertSimple

/-! ### `revert` -/

/-- `revert();` under the diamond: no state is reached. -/
theorem revertDiamond : dl!{ ⟨ revert(); ⟩ φ } ~[revertDiamond]~> dl!{ false } := rfl

/-- `revert();` under the box: every state reached satisfies anything. -/
theorem revertBox : dl!{ [ revert(); ] φ } ~[revertBox]~> dl![.box]{ true } := rfl

/-! ### `if`

`if (true)`, `if (false)` and `if (!ok)` have no rule of their own here: a literal is a
simple condition (`ifElseSplit`) and `!ok` is captured (`ifElseUnfold`). -/

/-- The program, both branches run. -/
theorem ifElseUnfold1 :
    dl![m]{
      { storage := save(storage, alice.age, 42) ‖ ageVal := 30 } ⟨[ if (alice.age > ageVal) { s0 = 1; } else { s1 = 1; }; ]⟩ φ }
    ~[ifElseUnfold]~> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 }
          ⟨[ bool se1 = alice.age > ageVal; if (se1) { s0 = 1; } else { s1 = 1; }; ]⟩ φ }
    ~[localValueDeclInitDrop]~> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 }
          ⟨[ se1 = alice.age > ageVal; if (se1) { s0 = 1; } else { s1 = 1; }; ]⟩ φ }
    ~[binopUnfoldLeft]~> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 }
          ⟨[ uint se2 = alice.age; se1 = se2 > ageVal; if (se1) { s0 = 1; } else { s1 = 1; }; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 }
          { se2 := find(storage, alice.age) } ⟨[ se1 = se2 > ageVal; if (se1) { s0 = 1; } else { s1 = 1; }; ]⟩ φ }
    ~[binopAssignment]~> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 }
          { se2 := find(storage, alice.age) } { se1 := se2 > ageVal } ⟨[ if (se1) { s0 = 1; } else { s1 = 1; }; ]⟩ φ }
    ~[ifElseSplit]~> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 }
          { se2 := find(storage, alice.age) }
            { se1 := se2 > ageVal }
              ((se1 ≐ true → ⟨[ s0 = 1; ]⟩ φ) ∧
                  (se1 ≐ false → ⟨[ s1 = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~*> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 }
          { se2 := find(storage, alice.age) }
            { se1 := se2 > ageVal }
              ((se1 ≐ true → { s0 := 1 } φ) ∧
                  (se1 ≐ false → ⟨[ s1 = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
  sol_chain

/-- The merge, the condition read and folded (`greater_literals`), and the branch it selects. -/
theorem ifElseUnfold2 :
    dl![m]{
      { storage := save(storage, alice.age, 42) ‖ ageVal := 30 }
        { se2 := find(storage, alice.age) }
          { se1 := se2 > ageVal }
            ((se1 ≐ true → { s0 := 1 } φ) ∧
                (se1 ≐ false → ⟨[ s1 = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~*> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 }
          { se2 := find(storage, alice.age) }
            { se1 := se2 > ageVal }
              ((se1 ≐ true → { s0 := 1 } φ) ∧
                  (se1 ≐ false → { s1 := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[sequentialToParallel]~> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 ‖ se2 := find(save(storage, alice.age, 42), alice.age) ‖
            se1 := find(save(storage, alice.age, 42), alice.age) > 30 }
          ((se1 ≐ true → { s0 := 1 } φ) ∧
              (se1 ≐ false → { s1 := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[findOnSave]~> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 ‖ se2 := 42 ‖ se1 := 42 > 30 }
          ((se1 ≐ true → { s0 := 1 } φ) ∧
              (se1 ≐ false → { s1 := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[greater_literals]~> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 ‖ se2 := 42 ‖ se1 := true }
          ((se1 ≐ true → { s0 := 1 } φ) ∧
              (se1 ≐ false → { s1 := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~[applyOnPV]~> dl![m]{
        { storage := save(storage, alice.age, 42) ‖ ageVal := 30 ‖ se2 := 42 ‖ se1 := true }
          ((true ≐ true → { s0 := 1 } φ) ∧
              (true ≐ false → { s1 := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false)) }
    ~[concrete]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ ageVal := 30 ‖ se2 := 42 ‖ se1 := true } { s0 := 1 } φ }
    ~[sequentialToParallel]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ ageVal := 30 ‖ se2 := 42 ‖ se1 := true ‖ s0 := 1 } φ } := by
  sol_chain

/-- `if (alice.age > ageVal) { s0 = 1; } else { s1 = 1; }` with `ageVal` 30, from a storage where `alice.age`
is 42: the condition captured (the row's rule), split on, the comparison folded to `true` (`greater_literals`),
the `then` branch kept (`applyOnPV`, `concrete`).  Two segments (`ifElseUnfold1`, `ifElseUnfold2`). -/
theorem ifElseUnfold :
    dl![m]{
      { storage := save(storage, alice.age, 42) ‖ ageVal := 30 } ⟨[ if (alice.age > ageVal) { s0 = 1; } else { s1 = 1; }; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ ageVal := 30 ‖ se2 := 42 ‖ se1 := true ‖ s0 := 1 } φ } :=
  (ifElseUnfold1 ..).leads.via (ifElseUnfold2 ..)
#last_line ifElseUnfold

/-- `if (ok) { s0 = 1; } else { s1 = 1; }` with `ok` `true`: both branches run, the condition read
(`applyOnRigid`), and the `then` branch kept (`concrete`). -/
theorem ifElseSplit :
    dl![m]{ { ok := true } ⟨[ if (ok) { s0 = 1; } else { s1 = 1; }; ]⟩ φ }
    ~[ifElseSplit]~> dl![m]{
        { ok := true }
          ((ok ≐ true → ⟨[ s0 = 1; ]⟩ φ) ∧
              (ok ≐ false → ⟨[ s1 = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ ok ≐ true ∨ ok ≐ false)) }
    ~*> dl![m]{
        { ok := true }
          ((ok ≐ true → { s0 := 1 } φ) ∧ (ok ≐ false → ⟨[ s1 = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ ok ≐ true ∨ ok ≐ false)) }
    ~*> dl![m]{
        { ok := true }
          ((ok ≐ true → { s0 := 1 } φ) ∧ (ok ≐ false → { s1 := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ ok ≐ true ∨ ok ≐ false)) }
    ~[applyOnRigid]~> dl![m]{
        (true ≐ true → { ok := true } { s0 := 1 } φ) ∧
          (true ≐ false → { ok := true } { s1 := 1 } φ) ∧
            ({ ok := true } ⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
    ~[sequentialToParallel]~> dl![m]{
        (true ≐ true → { ok := true ‖ s0 := 1 } φ) ∧
          (true ≐ false → { ok := true } { s1 := 1 } φ) ∧
            ({ ok := true } ⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
    ~[concrete]~> dl![m]{ { ok := true ‖ s0 := 1 } φ } := by
  sol_chain
#last_line ifElseSplit

end
end Solidity.Examples.Chains.StorageCoverage
