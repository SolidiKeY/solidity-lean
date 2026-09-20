import Solidity.Semantics

/-!
# Ports of `keyext.solidity.examples/taclets`: storage operations

Root/field/index reads and writes, copies, aliases, compound
assignments, increments/decrements, `delete`, and `push`/`pop`.

Adaptations from the `.key` sources:
- array-length premises (`1 < find(storage, values·size) ->`) become
  leading `push` statements that establish the length;
- local storage aliases use the names of the alias table in `AST.lean`
  (`p`, `acc`), e.g. `alicePath` becomes `p`;
- `--` cannot be a Lean token (it starts a comment), so decrement
  statements are built with `SoliditySyntax.incDecExpr` directly.
-/

namespace Solidity
namespace TacletExamples

/-- `storage-root-read-write.key` -/
example : (sol!{ < age = 34; result = age > (result == 34) }).Holds := by
  native_decide

/-- `storage-root-multiple-writes.key` -/
example :
    (sol!{ < age = 1; age = 2; result = age > (result == 2) }).Holds := by
  native_decide

/-- `storage-field-write-read.key` -/
example :
    (sol!{ < alice.age = 34; result = alice.age > (result == 34) }).Holds := by
  native_decide

/-- `storage-field-deep-write-read.key` /
`storage-field-decomposition.key` (also the goal example) -/
example :
    (sol!{ < alice.account.balance = 34; result = alice.account.balance >
           (result == 34) }).Holds := by
  native_decide

/-- `storage-field-deep-value.key` (the `consr` path decomposition
becomes an observable write-then-read) -/
example :
    (sol!{ < alice.account.token.value = 7;
             result = alice.account.token.value > (result == 7) }).Holds := by
  native_decide

/-- `storage-field-global-age.key` / `storage-field-read-store-root.key` -/
example :
    (sol!{ < alice.age = 17; total = alice.age; result = total >
           (result == 17) }).Holds := by
  native_decide

/-- `storage-root-copy-source.key` -/
example :
    (sol!{ < age = 34; balance = age; result = balance >
           (result == 34) }).Holds := by
  native_decide

/-- `storage-root-copy-struct.key` (deep copy, not aliasing) -/
example :
    (sol!{ < bob.age = 7; alice = bob; result = alice.age >
           (result == 7) }).Holds := by
  native_decide

/-- Copies are by value: mutating the source afterwards does not change
the copy (`storage-root-disjoint.key` flavor). -/
example :
    (sol!{ < bob.age = 7; alice = bob; bob.age = 9; result = alice.age >
           (result == 7) }).Holds := by
  native_decide

/-- `storage-field-disjoint-roots.key` -/
example :
    (sol!{ < alice.age = 1; bob.age = 2 >
           (alice.age == 1) && (bob.age == 2) }).Holds := by
  native_decide

/-- `storage-field-disjoint-fields.key` -/
example :
    (sol!{ < alice.account.balance = 1; alice.account.token.value = 2 >
           (alice.account.balance == 1) && (alice.account.token.value == 2)
    }).Holds := by
  native_decide

/-- `storage-field-copy-struct.key` -/
example :
    (sol!{ < bob.account.balance = 11;
             Account storage acc = bob.account;
             alice.account = acc;
             result = alice.account.balance > (result == 11) }).Holds := by
  native_decide

/-- `storage-index-root-array.key` (length premise via two pushes) -/
example :
    (sol!{ < values.push(); values.push();
             values[1] = 42; result = values[1] > (result == 42) }).Holds := by
  native_decide

/-- `storage-index-multiple-writes.key` (length premise via pushes) -/
example :
    (sol!{ < values.push(); values.push(); values.push(); values.push();
             values[3] = 5; values[3] = 8; result = values[3] >
           (result == 8) }).Holds := by
  native_decide

/-- `storage-index-root-mapping.key` -/
example :
    (sol!{ < balances[1] = 42; result = balances[1] >
           (result == 42) }).Holds := by
  native_decide

/-- `storage-matrix-write-read.key` / `storage-index-decomposition.key`
(nested arrays; lengths via pushes) -/
example :
    (sol!{ < matrix.push(); matrix.push(); matrix.push();
             matrix[2].push(); matrix[2].push(); matrix[2].push();
             matrix[2].push();
             matrix[2][3] = 99; result = matrix[2][3] >
           (result == 99) }).Holds := by
  native_decide

/-- `storage-index-decompose-after-push.key`: the pushed row starts
empty and is then extended and written. -/
example :
    (sol!{ < matrix.push();
             matrix[0].push(100); matrix[0][0] = 7; result = matrix[0][0] >
           (result == 7) }).Holds := by
  native_decide

/-- `storage-index-copysource-after-push.key` (`uint[][] storage m`
becomes `UintMatrix storage m`; the aggregate equality on `matrix[0]`
becomes element reads). -/
example :
    (sol!{ < values.push(5); values.push(6);
             UintMatrix storage m = matrix;
             m.push(); m[0] = values;
             result = matrix[0][1] >
           (matrix[0][0] == 5) && (result == 6) }).Holds := by
  native_decide

/-- `storage-index-array-out-of-bounds-box.key`: an out-of-bounds write
reverts, so the box judgment holds with postcondition `false`. -/
example : (sol!{ [ values[1] = 7 ] (false == true) }).Holds := by
  native_decide

/-- `storage-alias-rebind-alias.key` (`alicePath` ↦ `p`) -/
example :
    (sol!{ < Person storage p = alice;
             bob.age = 20;
             p = bob;
             result = p.age > (result == 20) }).Holds := by
  native_decide

/-- `storage-alias-rebind-original.key`: re-binding the alias leaves the
original untouched. -/
example :
    (sol!{ < uint before = alice.age;
             Person storage p = alice;
             bob.age = 20;
             p = bob;
             result = alice.age > (result == before) }).Holds := by
  native_decide

/-- `storage-alias-write-balance.key` -/
example :
    (sol!{ < Person storage p = alice;
             Account storage acc = p.account;
             acc.balance = 100;
             p.account.token.value = 3;
             result = alice.account.balance > (result == 100) }).Holds := by
  native_decide

/-- `storage-alias-write-token.key` -/
example :
    (sol!{ < Person storage p = alice;
             Account storage acc = p.account;
             acc.balance = 100;
             p.account.token.value = 3;
             result = alice.account.token.value > (result == 3) }).Holds := by
  native_decide

/-- `storage-field-read-bind-local.key` -/
example :
    (sol!{ < Account storage acc = alice.account;
             bob.account.balance = 42;
             acc = bob.account;
             result = acc.balance > (result == 42) }).Holds := by
  native_decide

/-- `storage-local-decl-skip.key` -/
example :
    (sol!{ < Person storage p; age = 7; result = age >
           (result == 7) }).Holds := by
  native_decide

/-- `storage-root-add-assign.key` -/
example :
    (sol!{ < age = 10; age += 5; result = age > (result == 15) }).Holds := by
  native_decide

/-- `storage-root-sub-assign.key` -/
example :
    (sol!{ < age = 10; age -= 4; result = age > (result == 6) }).Holds := by
  native_decide

/-- `storage-root-mul-assign.key` -/
example :
    (sol!{ < age = 6; age *= 3; result = age > (result == 18) }).Holds := by
  native_decide

/-- `storage-root-div-assign.key` -/
example :
    (sol!{ < age = 20; age /= 4; result = age > (result == 5) }).Holds := by
  native_decide

/-- `storage-root-mod-assign.key` -/
example :
    (sol!{ < age = 17; age %= 5; result = age > (result == 2) }).Holds := by
  native_decide

/-- `storage-field-add-assign.key` -/
example :
    (sol!{ < alice.age = 30; alice.age += 4; result = alice.age >
           (result == 34) }).Holds := by
  native_decide

/-- `storage-field-sub-assign.key` -/
example :
    (sol!{ < alice.age = 30; alice.age -= 5; result = alice.age >
           (result == 25) }).Holds := by
  native_decide

/-- `storage-field-mul-assign.key` -/
example :
    (sol!{ < alice.age = 7; alice.age *= 4; result = alice.age >
           (result == 28) }).Holds := by
  native_decide

/-- `storage-field-div-assign.key` -/
example :
    (sol!{ < alice.age = 30; alice.age /= 5; result = alice.age >
           (result == 6) }).Holds := by
  native_decide

/-- `storage-field-mod-assign.key` -/
example :
    (sol!{ < alice.age = 30; alice.age %= 7; result = alice.age >
           (result == 2) }).Holds := by
  native_decide

/-- `storage-field-deep-add-assign.key` -/
example :
    (sol!{ < alice.account.balance = 30; alice.account.balance += 4;
             result = alice.account.balance > (result == 34) }).Holds := by
  native_decide

/-- `storage-field-deep-sub-assign.key`,
`storage-field-deep-mul-assign.key`, `storage-field-deep-div-assign.key`,
`storage-field-deep-mod-assign.key` -/
example :
    (sol!{ < alice.account.balance = 30; alice.account.balance -= 4;
             result = alice.account.balance > (result == 26) }).Holds := by
  native_decide
example :
    (sol!{ < alice.account.balance = 30; alice.account.balance *= 4;
             result = alice.account.balance > (result == 120) }).Holds := by
  native_decide
example :
    (sol!{ < alice.account.balance = 30; alice.account.balance /= 4;
             result = alice.account.balance > (result == 7) }).Holds := by
  native_decide
example :
    (sol!{ < alice.account.balance = 30; alice.account.balance %= 4;
             result = alice.account.balance > (result == 2) }).Holds := by
  native_decide

/-- `storage-index-add-assign.key` -/
example :
    (sol!{ < values.push(); values.push();
             values[1] = 40; values[1] += 2; result = values[1] >
           (result == 42) }).Holds := by
  native_decide

/-- `storage-index-sub-assign.key` -/
example :
    (sol!{ < values.push(); values.push();
             values[1] = 40; values[1] -= 8; result = values[1] >
           (result == 32) }).Holds := by
  native_decide

/-- `storage-index-mul-assign.key` -/
example :
    (sol!{ < values.push(); values.push();
             values[1] = 5; values[1] *= 6; result = values[1] >
           (result == 30) }).Holds := by
  native_decide

/-- `storage-index-div-assign.key` -/
example :
    (sol!{ < values.push(); values.push();
             values[1] = 40; values[1] /= 8; result = values[1] >
           (result == 5) }).Holds := by
  native_decide

/-- `storage-index-mod-assign.key` -/
example :
    (sol!{ < values.push(); values.push();
             values[1] = 40; values[1] %= 6; result = values[1] >
           (result == 4) }).Holds := by
  native_decide

/-- A zero divisor in `/=` reverts (KeY `storageRootDivAssign` guard). -/
example : (sol!{ [ age = 10; age /= 0 ] (false == true) }).Holds := by
  native_decide

/-- `storage-root-preincrement.key` -/
example :
    (sol!{ < age = 10; ++age; result = age > (result == 11) }).Holds := by
  native_decide

/-- `storage-root-postincrement.key` (statement form) -/
example :
    (sol!{ < age = 10; age++; result = age > (result == 11) }).Holds := by
  native_decide

/-- `storage-root-postincrement-assign.key`: `x++` yields the old
value. -/
example :
    (sol!{ < age = 10; result = age++ > (result == 10) }).Holds := by
  native_decide

/-- `storage-root-preincrement-assign.key`: `++x` yields the new
value. -/
example :
    (sol!{ < age = 10; result = ++age > (result == 11) }).Holds := by
  native_decide

/-- `storage-root-postdecrement-assign.key`: `x--` yields the old value
(`--` is built explicitly: it cannot be a Lean token). -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ sstmt!{ age = 10 },
          Stmt.assign (splace!{ result })
            (SoliditySyntax.incDecExpr IncDec.postDec (sexpr!{ age })) ]⟩
      sexpr!{ (result == 10) }).Holds := by
  native_decide

/-- `storage-field-preincrement.key` -/
example :
    (sol!{ < alice.age = 30; ++alice.age; result = alice.age >
           (result == 31) }).Holds := by
  native_decide

/-- `storage-field-postincrement.key` -/
example :
    (sol!{ < alice.age = 30; alice.age++; result = alice.age >
           (result == 31) }).Holds := by
  native_decide

/-- `storage-field-postincrement-assign.key` -/
example :
    (sol!{ < alice.age = 30; result = alice.age++ >
           (result == 30) }).Holds := by
  native_decide

/-- `storage-field-preincrement-assign.key` -/
example :
    (sol!{ < alice.age = 30; result = ++alice.age >
           (result == 31) }).Holds := by
  native_decide

/-- `storage-field-predecrement.key` -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ sstmt!{ alice.age = 30 },
          Stmt.expr (SoliditySyntax.incDecExpr IncDec.preDec
            (sexpr!{ alice.age })),
          sstmt!{ result = alice.age } ]⟩
      sexpr!{ (result == 29) }).Holds := by
  native_decide

/-- `storage-field-postdecrement.key` -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ sstmt!{ alice.age = 30 },
          Stmt.expr (SoliditySyntax.incDecExpr IncDec.postDec
            (sexpr!{ alice.age })),
          sstmt!{ result = alice.age } ]⟩
      sexpr!{ (result == 29) }).Holds := by
  native_decide

/-- `storage-field-predecrement-assign.key` -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ sstmt!{ alice.age = 30 },
          Stmt.assign (splace!{ result })
            (SoliditySyntax.incDecExpr IncDec.preDec
              (sexpr!{ alice.age })) ]⟩
      sexpr!{ (result == 29) }).Holds := by
  native_decide

/-- `storage-deep-field-preincrement.key` -/
example :
    (sol!{ < alice.account.balance = 100; ++alice.account.balance;
             result = alice.account.balance > (result == 101) }).Holds := by
  native_decide

/-- `storage-deep-field-postincrement.key` -/
example :
    (sol!{ < alice.account.balance = 100; alice.account.balance++;
             result = alice.account.balance > (result == 101) }).Holds := by
  native_decide

/-- `storage-index-preincrement-assign.key` -/
example :
    (sol!{ < values.push(); values.push();
             values[1] = 40; result = ++values[1] >
           (result == 41) }).Holds := by
  native_decide

/-- `storage-index-preincrement.key` -/
example :
    (sol!{ < values.push(); values.push();
             values[1] = 40; ++values[1]; result = values[1] >
           (result == 41) }).Holds := by
  native_decide

/-- `storage-index-postincrement.key` -/
example :
    (sol!{ < values.push(); values.push();
             values[1] = 40; values[1]++; result = values[1] >
           (result == 41) }).Holds := by
  native_decide

/-- `storage-index-postincrement-assign.key` -/
example :
    (sol!{ < values.push(); values.push();
             values[1] = 40; result = values[1]++ >
           (result == 40) }).Holds := by
  native_decide

/-- `storage-index-predecrement.key` -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ sstmt!{ values.push() }, sstmt!{ values.push() },
          sstmt!{ values[1] = 40 },
          Stmt.expr (SoliditySyntax.incDecExpr IncDec.preDec
            (sexpr!{ values[1] })),
          sstmt!{ result = values[1] } ]⟩
      sexpr!{ (result == 39) }).Holds := by
  native_decide

/-- `storage-index-postdecrement.key` -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ sstmt!{ values.push() }, sstmt!{ values.push() },
          sstmt!{ values[1] = 40 },
          Stmt.expr (SoliditySyntax.incDecExpr IncDec.postDec
            (sexpr!{ values[1] })),
          sstmt!{ result = values[1] } ]⟩
      sexpr!{ (result == 39) }).Holds := by
  native_decide

/-- `storage-index-predecrement-assign.key` -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ sstmt!{ values.push() }, sstmt!{ values.push() },
          sstmt!{ values[1] = 40 },
          Stmt.assign (splace!{ result })
            (SoliditySyntax.incDecExpr IncDec.preDec
              (sexpr!{ values[1] })) ]⟩
      sexpr!{ (result == 39) }).Holds := by
  native_decide

/-- `storage-index-postdecrement-assign.key` -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ sstmt!{ values.push() }, sstmt!{ values.push() },
          sstmt!{ values[1] = 40 },
          Stmt.assign (splace!{ result })
            (SoliditySyntax.incDecExpr IncDec.postDec
              (sexpr!{ values[1] })) ]⟩
      sexpr!{ (result == 40) }).Holds := by
  native_decide

/-- `storage-root-predecrement.key` (`--` is built explicitly: it cannot
be a Lean token). -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ sstmt!{ age = 10 },
          Stmt.expr (SoliditySyntax.incDecExpr IncDec.preDec
            (sexpr!{ age })),
          sstmt!{ result = age } ]⟩
      sexpr!{ (result == 9) }).Holds := by
  native_decide

/-- `storage-field-postdecrement-assign.key` -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ sstmt!{ alice.age = 30 },
          sstmt!{ result = alice.age },
          Stmt.assign (splace!{ result })
            (SoliditySyntax.incDecExpr IncDec.postDec
              (sexpr!{ alice.age })) ]⟩
      sexpr!{ (result == 30) && (alice.age == 29) }).Holds := by
  native_decide

/-- `storage-root-delete.key` -/
example :
    (sol!{ < age = 10; delete age; result = age > (result == 0) }).Holds := by
  native_decide

/-- `storage-field-delete.key` -/
example :
    (sol!{ < alice.age = 30; delete alice.age; result = alice.age >
           (result == 0) }).Holds := by
  native_decide

/-- `storage-root-delete-struct.key` -/
example :
    (sol!{ < alice.age = 30; delete alice; result = alice.age >
           (result == 0) }).Holds := by
  native_decide

/-- `delNode` semantics (solkey `selectStDelNodeMap`): `delete` on a
struct resets value members but preserves mapping members. -/
example :
    (sol!{ < wallet.owner = 7; wallet.stash[1] = 42; delete wallet;
             result = wallet.stash[1] > (result == 42) }).Holds := by
  native_decide

/-- `delNode` semantics, value-member side: the same `delete` does reset
the struct's primitive members (solkey `selectStDelNodePrim`). -/
example :
    (sol!{ < wallet.owner = 7; wallet.stash[1] = 42; delete wallet;
             result = wallet.owner > (result == 0) }).Holds := by
  native_decide

/-- `storage-index-delete.key` -/
example :
    (sol!{ < values.push(); values.push();
             values[1] = 7; delete values[1]; result = values[1] >
           (result == 0) }).Holds := by
  native_decide

/-- `storage-push-empty.key` -/
example :
    (sol!{ < values.push(); values.push(); values.push();
             result = values[2] > (result == 0) }).Holds := by
  native_decide

/-- `storage-push-value.key` -/
example :
    (sol!{ < values.push(); values.push(); values.push(42);
             result = values[2] > (result == 42) }).Holds := by
  native_decide

/-- `storage-push-nonsimple-arg.key` -/
example :
    (sol!{ < uint x = 40; uint y = 2; values.push(x + y);
             result = values[0] > (result == 42) }).Holds := by
  native_decide

/-- `storage-push-return-assign.key`: push-lvalue form. -/
example :
    (sol!{ < values.push(); values.push(); values.push() = 42;
             result = values[2] > (result == 42) }).Holds := by
  native_decide

/-- `storage-push-local-bind.key`: bind a local to the pushed slot. -/
example :
    (sol!{ < persons.push(); persons.push();
             Person storage p; p = persons.push();
             p.age = 5; result = persons[2].age > (result == 5) }).Holds := by
  native_decide

/-- `storage-pop-nonempty.key` (observable via out-of-bounds revert on
the popped slot). -/
example :
    (sol!{ < values.push(); values.push(); values.pop();
             result = values[0] > (result == 0) }).Holds := by
  native_decide
example :
    (sol!{ [ values.push(); values.push(); values.pop();
             result = values[1] ] (false == true) }).Holds := by
  native_decide

/-- `storage-pop-empty-box.key`: pop on an empty array reverts. -/
example : (sol!{ [ values.pop() ] (false == true) }).Holds := by
  native_decide

/-- `storage-pop-after-push.key` -/
example :
    (sol!{ [ values.push(); values.pop(); result = values[0] ]
           (false == true) }).Holds := by
  native_decide

/-! ### A popped slot keeps its mappings

solkey's `TestSuite.testDeepPopDoesNotResetMappingMember`. `pop()`
implicitly `delete`s the removed element and `delete` never clears a
mapping member, so the slot the next `push()` recycles still holds the
entries — solc's behaviour, and upstream's `storagePopSave` /
`storagePushLengthSave`, both of which write `delAt` at that slot.
`Semantics.pushSlot` is that `delAt`.

The ported obligation (`Corpus/Wp/TestSuite.lean`) is `open` for a
reason that has nothing to do with this: the `sol!` grammar reads
`ledgerUses[0].ledger.balances` as one dotted field name, so the port's
spelling never reaches the mapping. Splitting the two hops with a
storage alias is the same program, and it closes. -/
example :
    (sol!{ < (ledgerUses@@LedgerUseArray).push();
             Ledger storage l = ledgerUses@@LedgerUseArray[0].ledger;
             l@@Ledger.balances[1] = 10;
             (ledgerUses@@LedgerUseArray).pop();
             (ledgerUses@@LedgerUseArray).push();
             Ledger storage l2 = ledgerUses@@LedgerUseArray[0].ledger;
             result = l2@@Ledger.balances[1] > (result == 10) }).Holds
      Semantics.State.testSuiteStore := by
  native_decide

/-- …while the value members of the recycled slot *are* reset, which is
what keeps `storage-push-empty.key` above true: the slot is cleared, not
kept. -/
example :
    (sol!{ < (ledgerUses@@LedgerUseArray).push();
             Ledger storage l = ledgerUses@@LedgerUseArray[0].ledger;
             l@@Ledger.nonce = 7;
             (ledgerUses@@LedgerUseArray).pop();
             (ledgerUses@@LedgerUseArray).push();
             Ledger storage l2 = ledgerUses@@LedgerUseArray[0].ledger;
             result = l2@@Ledger.nonce > (result == 0) }).Holds
      Semantics.State.testSuiteStore := by
  native_decide

/-- `storage-index-delete-mapping-bool.key` flavor on `flags`. -/
example :
    (sol!{ < flags[3] = true; delete flags[3]; result = flags[3] >
           (result == false) }).Holds := by
  native_decide

/-- `storage-index-delete-mapping-struct.key` flavor on `folks`. -/
example :
    (sol!{ < folks[1].age = 44; delete folks[1]; result = folks[1].age >
           (result == 0) }).Holds := by
  native_decide

/-- If-then-else on a captured condition (`ifThenElseRules.key`). -/
example :
    (sol!{ < age = 10;
             if ((age < 20)) { result = 1 } else { result = 2 } >
           (result == 1) }).Holds := by
  native_decide

/-- `assert` holds: execution continues (`assertSimple`, "Holds"). -/
example :
    (sol!{ < age = 10; assert((age == 10)); result = 1 >
           (result == 1) }).Holds := by
  native_decide

/-- `assert` violated: reverts, so only the box judgment holds
(`assertSimple`, "Violated"; `MinimalAssert.sol` flavor). -/
example : (sol!{ [ assert(false); result = 1 ] (false == true) }).Holds := by
  native_decide
example :
    ¬ (sol!{ < assert(false); result = 1 > (result == 1) }).Holds := by
  native_decide

/-- `require` holds: execution continues (`requireSimple`, "Holds"). -/
example :
    (sol!{ < age = 10; require((age == 10)); result = 1 >
           (result == 1) }).Holds := by
  native_decide

/-- `require` violated: reverts. In the box modality the judgment holds
vacuously (`requireSimple`, "Reverts": box `c → φ`); in the diamond it
fails (diamond `c ∧ φ`) — solkey `docs/require-assert.md`. -/
example : (sol!{ [ require(false); result = 1 ] (false == true) }).Holds := by
  native_decide
example :
    ¬ (sol!{ < require(false); result = 1 > (result == 1) }).Holds := by
  native_decide

end TacletExamples
end Solidity
