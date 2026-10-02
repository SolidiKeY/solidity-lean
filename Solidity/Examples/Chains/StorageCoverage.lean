import Solidity.Calculus.Chains
import Solidity.Calculus.Close

/-!
# Storage rule coverage: one step per rule

A table, one row per rule: a statement, and the line its rule gives, `φ ~[r]~> ψ`
(`Examples/ChainNotation.lean` says how to read one).  The program is `Coverage`,
the contract of the printed rows.  The rule's name is Lean's; where the printed
trace names it differently, the printed name follows in a comment.

Stand-ins: `alice.account.tokens` is `bucket.tokens`, and `alice.account.tokens[i] = tokVal;`
a write of a `uint` into `basket.items`; `tokVal`, `pVal` are `uint` where the row's source is a
value (a `Token` or `Person` value is no source here).  A statement holding a call
(`makeValue()`) is the elaborator's first step, an equation, not a rule; so is a `++` in an operand.
A literal or negated condition has no rule here (`if (true)` is `ifElseSplit`).
-/

namespace Solidity.Examples.Chains.StorageCoverage

/-- The state of the rows: `values` and `tokens` arrays, `ledgers` an array of mappings,
`tokenById` and `personById` mappings, `flag` a boolean. -/
def Coverage : Contract := contract!{
  uint total; uint age; bool flag; uint[] values; mapping(uint => uint) balances;
  Person alice; Person bob; Person[] people; mapping(uint => Person) personById;
  Token[] tokens; mapping(uint => Token) tokenById; mapping(uint => uint)[] ledgers;
  TokenBucket bucket; Basket basket;
  function makeValue() returns (uint) { return total; }
  function checkBalance() returns (bool) { return true; }
  function checkInvariant() returns (bool) { return true; }
}

local instance : InContract := ⟨Coverage⟩

/-! ### Field and root writes -/

example : dl!{ ⟨ alice.account.balance = balanceVal; ⟩ true }
    ~[storageFieldWrite_unfold_leftFst]~>
      dl!{ ⟨ uint se1 = balanceVal; Account storage sp1 = alice.account; sp1.balance = se1; ⟩ true } := rfl

example : dl!{ ⟨ alice.account = acc; ⟩ true where Account storage acc }
    ~[storageFieldWriteCopySource]~>
      dl!{ { storage := save(storage, alice.account, find(storage, acc)) } ⟨⟩ true
        where Account storage acc } := rfl

example : dl!{ ⟨ alice.age = ageVal; ⟩ true }
    ~[storageFieldWriteSave]~> dl!{ { storage := save(storage, alice.age, ageVal) } ⟨⟩ true } := rfl

example : dl!{ ⟨ alice = bob; ⟩ true }
    ~[storageRootWriteCopySource]~> dl!{ { storage := store(storage, alice, find(storage, bob)) } ⟨⟩ true } :=
  rfl

-- `pVal` is a `uint` and the root `total`: a `Person` value is no source.
example : dl!{ ⟨ total = pVal; ⟩ true }
    ~[storageRootWriteStore]~> dl!{ { storage := store(storage, total, pVal) } ⟨⟩ true } := rfl

/-! ### Declarations and rebinding -/

example : dl!{ ⟨ Account storage acc = alice.account; ⟩ true }
    ~[storageLocalDeclInitDrop]~> dl!{ ⟨ acc = alice.account; ⟩ true } := rfl

example : dl!{ ⟨ uint v = alice.age; ⟩ true }
    ~[localValueDeclInitDrop]~> dl!{ ⟨ v = alice.age; ⟩ true } := rfl

example : dl!{ ⟨ Account storage acc; ⟩ true } ~[storageLocalDeclSkip]~> dl!{ ⟨⟩ true } := rfl

example : dl!{ ⟨ uint v; ⟩ true } ~[valueDeclSkip]~> dl!{ { v := 0 } ⟨⟩ true } := rfl

example : dl!{ ⟨ p = bob; ⟩ true where Person storage p }
    ~[storageLocalRootRebind]~> dl!{ { p := bob } ⟨⟩ true where Person storage p } := rfl

/-! ### Field and root reads -/

example : dl!{ ⟨ v = alice.account.balance; ⟩ true }
    ~[storageFieldRead_unfold_rightFst]~>
      dl!{ ⟨ Account storage sp1 = alice.account; v = sp1.balance; ⟩ true } := rfl

example : dl!{ ⟨ acc = bob.account; ⟩ true where Account storage acc }
    ~[storageFieldReadBindLocalRoot]~>
      dl!{ { acc := bob.account } ⟨⟩ true where Account storage acc } := rfl

example : dl!{ ⟨ account = bob.account; ⟩ true where Account storage account }
    ~[storageFieldReadBindLocalRoot]~>
      dl!{ { account := bob.account } ⟨⟩ true where Account storage account } := rfl

example : dl!{ ⟨ v = alice.age; ⟩ true }
    ~[storageFieldReadFind]~> dl!{ { v := find(storage, alice.age) } ⟨⟩ true } := rfl

example : dl!{ ⟨ v = total; ⟩ true }
    ~[storageRootReadSelect]~> dl!{ { v := select(storage, total) } ⟨⟩ true } := rfl

/-! ### `delete` -/

example : dl!{ ⟨ delete alice.account.token; ⟩ true }
    ~[storageFieldDelete_unfold_leftFst]~>
      dl!{ ⟨ Account storage sp1 = alice.account; delete sp1.token; ⟩ true } := rfl

-- `bucket.tokens` for `alice.account.tokens`.
example : dl!{ ⟨ delete bucket.tokens[i]; ⟩ true }
    ~[storageIndexDelete_unfold_leftFst]~>
      dl!{ ⟨ Token[] storage sp1 = bucket.tokens; delete sp1[i]; ⟩ true } := rfl

example : dl!{ ⟨ delete alice; ⟩ true }
    ~[storageRootDelete]~> dl!{ { storage := delAt(storage, alice) } ⟨⟩ true } := rfl

example : dl!{ ⟨ delete alice.account; ⟩ true }
    ~[storageFieldDelete]~> dl!{ { storage := delAt(storage, alice.account) } ⟨⟩ true } := rfl

example : dl!{ ⟨ delete tokenById[id]; ⟩ true }
    ~[storageIndexDelete]~> dl!{ { storage := delAt(storage, tokenById[id]) } ⟨⟩ true } := rfl

example : dl!{ ⟨ delete tokens[i]; ⟩ true }
    ~[storageIndexArrayDelete]~> dl!{ { storage := delAt(storage, tokens[i]) } ⟨⟩ true } := rfl

/-! ### Writes through a receiver or an index that is not simple -/

-- `basket.items[i] = tokVal;` stands for `alice.account.tokens[i] = tokVal;`.
example : dl!{ ⟨ basket.items[i] = tokVal; ⟩ true }
    ~[storageIndexWriteCaptureAllComplexRecv]~>
      dl!{ ⟨ uint se1 = tokVal; uint[] storage sp1 = basket.items; uint ie1 = i; sp1[ie1] = se1; ⟩ true } :=
  rfl

example : dl!{ ⟨ alice.account.token = tokRef; ⟩ true where Token storage tokRef }
    ~[storageFieldWriteStorageRef_unfold_leftFst]~>
      dl!{ ⟨ Account storage sp1 = alice.account; sp1.token = tokRef; ⟩ true where Token storage tokRef } := rfl

-- `bucket.tokens` for `alice.account.tokens`.
example : dl!{ ⟨ bucket.tokens[i] = tokRef; ⟩ true where Token storage tokRef }
    ~[storageIndexWriteStorageRefCaptureAllComplexRecv]~>
      dl!{ ⟨ Token[] storage sp1 = bucket.tokens; uint ie1 = i; sp1[ie1] = tokRef; ⟩ true
        where Token storage tokRef } := rfl

-- The `++i` is the elaborator's: captured before the statement.
example : dl!{ ⟨ values[++i] = val; ⟩ true }
    = dl!{ ⟨ uint se1 = val; uint se2; se2 = ++i; values[se2] = se1; ⟩ true } := rfl

example : dl!{ ⟨ tokens[++i] = tokRef; ⟩ true where Token storage tokRef }
    = dl!{ ⟨ uint se1; se1 = ++i; tokens[se1] = tokRef; ⟩ true where Token storage tokRef } := rfl

/-! ### Writes with a source that is not simple -/

example : dl!{ ⟨ alice.age = ageVal + 1; ⟩ true }
    ~[fieldWriteValueRhsCapture]~> dl!{ ⟨ uint se1 = ageVal + 1; alice.age = se1; ⟩ true } := rfl

-- The call is the elaborator's.
example : dl!{ ⟨ values[i] = makeValue(); ⟩ true }
    = dl!{ ⟨ uint se1; se1 = makeValue(); values[i] = se1; ⟩ true } := rfl

example : dl!{ ⟨ total = makeValue(); ⟩ true }
    = dl!{ ⟨ uint se1; se1 = makeValue(); total = se1; ⟩ true } := rfl

-- printed `storageFieldWriteCaptureSrc`
example : dl!{ ⟨ alice.account = bob.account; ⟩ true }
    ~[storageFieldRead_unfold_rightSndResult]~>
      dl!{ ⟨ Account storage sp1 = bob.account; alice.account = sp1; ⟩ true } := rfl

-- printed `storageIndexWriteStorageRefRhsCapture`: the receiver `bob.account` is unfolded first.
example : dl!{ ⟨ tokens[i] = bob.account.token; ⟩ true }
    ~[storageFieldRead_unfold_rightFst]~>
      dl!{ ⟨ Account storage sp1 = bob.account; tokens[i] = sp1.token; ⟩ true } := rfl

/-! ### A write at an index: copy or save -/

example : dl!{ ⟨ tokens[i] = tokRef; ⟩ true where Token storage tokRef }
    ~[storageIndexWriteArrayCopySource]~>
      dl!{ { storage := save(storage, tokens[i], find(storage, tokRef)) } ⟨⟩ true
        where Token storage tokRef } := rfl

example : dl!{ ⟨ tokenById[id] = tokRef; ⟩ true where Token storage tokRef }
    ~[storageIndexWriteMappingCopySource]~>
      dl!{ { storage := save(storage, tokenById[id], find(storage, tokRef)) } ⟨⟩ true
        where Token storage tokRef } := rfl

-- `values[i] = tokVal;` stands for `tokens[i] = tokVal;`.
example : dl!{ ⟨ values[i] = tokVal; ⟩ true }
    ~[storageIndexWriteArraySave]~> dl!{ { storage := save(storage, values[i], tokVal) } ⟨⟩ true } := rfl

example : dl!{ ⟨ balances[account] = amount; ⟩ true }
    ~[storageIndexWriteMappingSave]~>
      dl!{ { storage := save(storage, balances[account], amount) } ⟨⟩ true } := rfl

/-! ### Reads at an index -/

-- `bucket.tokens` for `alice.account.tokens`.
example : dl!{ ⟨ tok = bucket.tokens[i]; ⟩ true where Token storage tok }
    ~[storageIndexRead_unfold_rightFst]~>
      dl!{ ⟨ Token[] storage sp1 = bucket.tokens; tok = sp1[i]; ⟩ true where Token storage tok } := rfl

example : dl!{ ⟨ tok = tokens[++i]; ⟩ true where Token storage tok }
    = dl!{ ⟨ uint se1; se1 = ++i; tok = tokens[se1]; ⟩ true where Token storage tok } := rfl

example : dl!{ ⟨ tok = tokens[i]; ⟩ true where Token storage tok }
    ~[storageIndexReadArrayBindLocalRoot]~> dl!{ { tok := tokens[i] } ⟨⟩ true where Token storage tok } := rfl

example : dl!{ ⟨ m = ledgers[i]; ⟩ true where mapping(uint => uint) storage m }
    ~[storageIndexReadArrayBindLocalRootMappingElement]~>
      dl!{ { m := ledgers[i] } ⟨⟩ true where mapping(uint => uint) storage m } := rfl

example : dl!{ ⟨ tok = tokenById[id]; ⟩ true where Token storage tok }
    ~[storageIndexReadMappingBindLocalRoot]~>
      dl!{ { tok := tokenById[id] } ⟨⟩ true where Token storage tok } := rfl

example : dl!{ ⟨ alice = people[i]; ⟩ true }
    ~[storageIndexReadArrayStoreRoot]~>
      dl!{ { storage := store(storage, alice, find(storage, people[i])) } ⟨⟩ true } := rfl

example : dl!{ ⟨ alice = personById[id]; ⟩ true }
    ~[storageIndexReadMappingStoreRoot]~>
      dl!{ { storage := store(storage, alice, find(storage, personById[id])) } ⟨⟩ true } := rfl

example : dl!{ ⟨ v = values[i]; ⟩ true }
    ~[storageIndexReadArrayFind]~> dl!{ { v := find(storage, values[i]) } ⟨⟩ true } := rfl

example : dl!{ ⟨ v = balances[account]; ⟩ true }
    ~[storageIndexReadMappingFind]~> dl!{ { v := find(storage, balances[account]) } ⟨⟩ true } := rfl

/-! ### `push` -/

-- `bucket.tokens` for `alice.account.tokens`.
example : dl!{ ⟨ bucket.tokens.push(tok); ⟩ true where Token storage tok }
    ~[storagePushValue_unfold_leftFstReceiver]~>
      dl!{ ⟨ Token[] storage sp1 = bucket.tokens; sp1.push(tok); ⟩ true where Token storage tok } := rfl

example : dl!{ ⟨ values.push(makeValue()); ⟩ true }
    = dl!{ ⟨ uint se1; se1 = makeValue(); values.push(se1); ⟩ true } := rfl

example : dl!{ ⟨ tokens.push(tokRef); ⟩ true where Token storage tokRef }
    ~[storagePushValueCopySource]~>
      dl!{ { storage := save(save(storage, tokens[tokens.length], find(storage, tokRef)), tokens.length,
          tokens.length + 1) } ⟨⟩ true where Token storage tokRef } := rfl

example : dl!{ ⟨ values.push(valueVal); ⟩ true }
    ~[storagePushValueSave]~>
      dl!{ { storage := save(save(storage, values[values.length], valueVal), values.length,
          values.length + 1) } ⟨⟩ true } := rfl

example : dl!{ ⟨ bucket.tokens.push(); ⟩ true }
    ~[storagePush_unfold_leftFstReceiver]~>
      dl!{ ⟨ Token[] storage sp1 = bucket.tokens; sp1.push(); ⟩ true } := rfl

example : dl!{ ⟨ values.push(); ⟩ true }
    ~[storagePushLengthSave]~>
      dl!{ { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) } ⟨⟩ true } :=
  rfl

example : dl!{ ⟨ tokens.push(); ⟩ true }
    ~[storagePushLengthSaveReferenceElement]~>
      dl!{ { storage := save(storage, tokens.length, tokens.length + 1) } ⟨⟩ true } := rfl

/-! ### `push` bound to a local -/

example : dl!{ ⟨ sp = bucket.tokens.push(); ⟩ true where Token storage sp }
    ~[storageLocalRootPush_unfold_leftFstReceiver]~>
      dl!{ ⟨ Token[] storage sp1 = bucket.tokens; sp = sp1.push(); ⟩ true where Token storage sp } := rfl

example : dl!{ ⟨ sp = tokens.push(); ⟩ true where Token storage sp }
    ~[storageLocalRootPushBind]~>
      dl!{ { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] } ⟨⟩ true
        where Token storage sp } := rfl

example : dl!{ ⟨ m = ledgers.push(); ⟩ true where mapping(uint => uint) storage m }
    ~[storageLocalRootPushBindMappingElement]~>
      dl!{ { storage := save(storage, ledgers.length, ledgers.length + 1) ‖ m := ledgers[ledgers.length] } ⟨⟩ true
        where mapping(uint => uint) storage m } := rfl

/-! ### `pop` -/

-- `bucket.tokens` for `alice.account.tokens`.
example : dl!{ ⟨ bucket.tokens.pop(); ⟩ true }
    ~[storagePop_unfold_leftFstReceiver]~>
      dl!{ ⟨ Token[] storage sp1 = bucket.tokens; sp1.pop(); ⟩ true } := rfl

example : dl!{ ⟨ tokens.pop(); ⟩ true }
    ~[storagePopSave]~>
      dl!{ { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) } ⟨⟩ true } :=
  rfl

example : dl!{ ⟨ ledgers.pop(); ⟩ true }
    ~[storagePopSaveMappingElement]~>
      dl!{ { storage := save(storage, ledgers.length, ledgers.length - 1) } ⟨⟩ true } := rfl

/-! ### `require` and `assert` -/

-- The call is the elaborator's; the capture rule itself fires on a condition
-- that is no simple expression, a state variable.
example : dl!{ ⟨ require(checkBalance()); ⟩ true }
    = dl!{ ⟨ bool se1; se1 = checkBalance(); require(se1); ⟩ true } := rfl

example : dl!{ ⟨ require(flag); ⟩ true }
    ~[requireConditionCapture]~> dl!{ ⟨ bool se1 = flag; require(se1); ⟩ true } := rfl

example : dl!{ ⟨ assert(checkInvariant()); ⟩ true }
    = dl!{ ⟨ bool se1; se1 = checkInvariant(); assert(se1); ⟩ true } := rfl

example : dl!{ ⟨ assert(flag); ⟩ true }
    ~[assertConditionCapture]~> dl!{ ⟨ bool se1 = flag; assert(se1); ⟩ true } := rfl

example : dl!{ ⟨ require(ok); ⟩ true where bool ok }
    ~[requireSimple]~>
      dl!{ (ok ≐ true → ⟨⟩ true) ∧ (ok ≐ false → ⟨ revert(); ⟩ true) ∧
        (⟨ revert(); ⟩ false ∨ ok ≐ true ∨ ok ≐ false) where bool ok } := rfl

example : dl!{ ⟨ assert(ok); ⟩ true where bool ok }
    ~[assertSimple]~>
      dl!{ (ok ≐ true → ⟨⟩ true) ∧ (ok ≐ false → ⟨ revert(); ⟩ true) ∧
        (⟨ revert(); ⟩ false ∨ ok ≐ true ∨ ok ≐ false) where bool ok } := rfl

/-! ### `revert` -/

example (φ : Post Coverage) : dl!{ ⟨ revert(); ⟩ φ } ~[revertDiamond]~> dl!{ false } := rfl

example (φ : Post Coverage) : dl!{ [ revert(); ] φ } ~[revertBox]~> dl![.box]{ true } := rfl

/-! ### `if`

`if (true)`, `if (false)` and `if (!ok)` have no rule of their own here: a literal is a
simple condition (`ifElseSplit`) and `!ok` is captured (`ifElseUnfold`). -/

example : dl!{ ⟨ if (alice.age > ageVal) { s0 = 1; } else { s1 = 1; }; ⟩ true }
    ~[ifElseUnfold]~>
      dl!{ ⟨ bool se1 = alice.age > ageVal; if (se1) { s0 = 1; } else { s1 = 1; }; ⟩ true } := rfl

example : dl!{ ⟨ if (ok) { s0 = 1; } else { s1 = 1; }; ⟩ true where bool ok }
    ~[ifElseSplit]~>
      dl!{ (ok ≐ true → ⟨ s0 = 1; ⟩ true) ∧ (ok ≐ false → ⟨ s1 = 1; ⟩ true) ∧
        (⟨ revert(); ⟩ false ∨ ok ≐ true ∨ ok ≐ false) where bool ok } := rfl

end Solidity.Examples.Chains.StorageCoverage
