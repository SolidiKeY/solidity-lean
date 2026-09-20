import Solidity.Calculus.Rules
import Solidity.Semantics

/-!
# Concrete validation of the unfold rules against the executable semantics

For every rule whose `ruleEffect` residual block is non-empty (the
unfold/capture/split rules), this file exhibits a concrete statement
matching the rule's condition and proves by evaluation that the original
statement and the rule's own residual block (`(ruleEffect r).block`)
validate the same discriminating postcondition from `State.exampleStore`.
Requiring both runs to succeed (`check = true`, diamond modality unless
noted) rules out vacuous stuck-vs-stuck agreement.

Terminal rules (empty residual) are not re-tested here: their semantic
content is `execStmt` itself, exercised by `Examples/Taclets/`.

Operand notes: `WrappedExpr.simple` holds only for bare variables and
literals, so complex operands below are storage/memory reads, operators,
or `++`/`--` — all interpreter-evaluable. Uninterpreted calls would make
both runs stuck and the validation vacuous.

Op-indexed families are validated on representative instances (an
arithmetic op, the guarded `div`, a comparison, and the short-circuit
connectives where the rule admits them); the residual template is
identical for the remaining ops.

The `*_primitive` variants exercise `Rules.valueCaptureKind`: a
primitive-typed memory read is captured into a typed stack temporary
(`T pv = nse;`), not a memory declaration — a memory declaration can
only bind an object identity, so the previous kind-directed capture got
stuck under the interpreter.
-/

namespace Solidity
namespace RuleValidation

open Rules SoliditySyntax

/-- `check = true` for the given modality, block, and postcondition from
`Semantics.State.exampleStore`. -/
abbrev validated (sm : SolidityModality) (blk : Block) (post : WrappedExpr) :
    Prop :=
  (SolidityJudgment.mk ⟨sm, blk⟩ post).check = true

/-- The validation statement: after `setup`, the original statement and
the rule's residual block both establish `post`. -/
abbrev Validates (rule : RuleName) (setup : Block) (stmt : Stmt)
    (post : WrappedExpr)
    (hcond : (ruleEffect rule).cond stmt)
    (sm : SolidityModality := .diamond) : Prop :=
  validated sm (setup ++ [stmt]) post ∧
    validated sm (setup ++ (ruleEffect rule).block stmt hcond) post

/-! ## Manual variables

Memory-array and memory-struct shapes the name tables in
`SoliditySyntax` do not cover. The declarations deep-copy from the
storage globals (`copySt`) or allocate defaults. -/

def uintArrayTy : Ty := Ty.ref (RefTy.array Ty.uint)
def uintMatrixTy : Ty := Ty.ref (RefTy.array uintArrayTy)
def personArrayTy : Ty := Ty.ref (RefTy.array StandardExample.personTy)

/-- `uint[][] memory mm = matrix;` -/
def mm : WrappedExpr := varExpr Kind.memory uintMatrixTy "mm"
def mmDecl : Stmt := Stmt.memoryDecl uintMatrixTy "mm" (some (rootExpr "matrix"))

/-- `uint[] memory mrow = values;` -/
def mrow : WrappedExpr := varExpr Kind.memory uintArrayTy "mrow"
def mrowDecl : Stmt := Stmt.memoryDecl uintArrayTy "mrow" (some (rootExpr "values"))

/-- `Person[] memory ps = people;` -/
def ps : WrappedExpr := varExpr Kind.memory personArrayTy "ps"
def psDecl : Stmt := Stmt.memoryDecl personArrayTy "ps" (some (rootExpr "people"))

/-- `Token memory mtok;` -/
def mtok : WrappedExpr := varExpr Kind.memory StandardExample.tokenTy "mtok"
def mtokDecl : Stmt := Stmt.memoryDecl StandardExample.tokenTy "mtok" none

/-- `Token memory mtok2 = alice.account.token;` target of the
storage-to-memory declaration unfold. -/
def mtok2 : WrappedExpr := varExpr Kind.memory StandardExample.tokenTy "mtok2"

def iE : WrappedExpr := rootExpr "i"
def amountE : WrappedExpr := rootExpr "amount"

def eqE (l r : WrappedExpr) : WrappedExpr := binopExpr .eqB l r
def lit (v : Int) : WrappedExpr := intLitExpr v

/-! ## Storage write/read unfolds -/

theorem storageFieldWriteUnfoldLeftFst_valid :
    Validates .storageFieldWriteUnfoldLeftFst
      sblock!{ uint amount = 7 }
      sstmt!{ alice.account.balance = amount }
      sexpr!{ (alice.account.balance == 7) }
      (by change _ = true ∧ _ = true ∧ ¬ _ = true; decide) := by
  native_decide

theorem storageLocalDeclInitDrop_valid :
    Validates .storageLocalDeclInitDrop
      sblock!{ alice.account.balance = 3 }
      (Stmt.storageDecl StandardExample.accountTy "acc"
        (some (sexpr!{ alice.account })))
      sexpr!{ (acc.balance == 3) }
      (by change _ = true; decide) := by
  native_decide

theorem storageFieldReadUnfoldRightFst_valid :
    Validates .storageFieldReadUnfoldRightFst
      sblock!{ alice.account.balance = 4; uint amount = 0 }
      sstmt!{ amount = alice.account.balance }
      sexpr!{ (amount == 4) }
      (by change _ = true ∧ ¬ (_ = Kind.memory ∧ _ = true); decide) := by
  native_decide

theorem storageFieldReadUnfoldRightSndResult_valid :
    Validates .storageFieldReadUnfoldRightSndResult
      sblock!{ bob.age = 9 }
      sstmt!{ alice.account.balance = bob.age }
      sexpr!{ (alice.account.balance == 9) }
      (by change _ = true ∧ _ = true ∧ _ = true; decide) := by
  native_decide

/-! ## Storage delete unfolds -/

theorem storageDeleteComplexTarget_field_valid :
    Validates .storageDeleteComplexTarget
      sblock!{ alice.account.balance = 5 }
      sstmt!{ delete alice.account.balance }
      sexpr!{ (alice.account.balance == 0) }
      (by change _ = true; decide) := by
  native_decide

theorem storageDeleteComplexTarget_index_valid :
    Validates .storageDeleteComplexTarget
      sblock!{ uint i = 0; values.push(1); values.push(2) }
      sstmt!{ delete values[i + 1] }
      sexpr!{ (values[1] == 0) && (values[0] == 1) }
      (by change _ = true ∨ (_ = true ∧ _ = true); decide) := by
  native_decide

/-! ## Storage indexed write/read unfolds -/

theorem storageIndexWriteUnfoldLeftFst_valid :
    Validates .storageIndexWriteUnfoldLeftFst
      sblock!{ uint i = 0; uint amount = 7; matrix.push(); matrix[i].push(3) }
      sstmt!{ matrix[i][i] = amount }
      sexpr!{ (matrix[i][i] == 7) }
      (by change _ = true ∧ _ = true; decide) := by
  native_decide

theorem storageIndexWriteUnfoldLeftSndIndex_valid :
    Validates .storageIndexWriteUnfoldLeftSndIndex
      sblock!{ uint i = 0; uint amount = 7; values.push(1); values.push(2) }
      sstmt!{ values[i + 1] = amount }
      sexpr!{ (values[1] == 7) }
      (by change _ = true ∧ _ = true ∧ _ = true ∧ ¬ _ = true; decide) := by
  native_decide

theorem storageIndexReadUnfoldRightFst_valid :
    Validates .storageIndexReadUnfoldRightFst
      sblock!{ uint i = 0; uint amount = 0; matrix.push(); matrix[i].push(3) }
      sstmt!{ amount = matrix[i][i] }
      sexpr!{ (amount == 3) }
      (by change _ = true ∧ ¬ (_ = Kind.memory ∧ _ = true); decide) := by
  native_decide

theorem storageIndexReadUnfoldRightSndIndex_valid :
    Validates .storageIndexReadUnfoldRightSndIndex
      sblock!{ uint i = 0; uint amount = 0; values.push(1); values.push(2) }
      sstmt!{ amount = values[i + 1] }
      sexpr!{ (amount == 2) }
      (by change _ = true ∧ _ = true ∧ ¬ (_ = Kind.memory ∧ _ = true)
          decide) := by
  native_decide

theorem storageIndexReadUnfoldRightSndResult_valid :
    Validates .storageIndexReadUnfoldRightSndResult
      sblock!{ uint i = 0; values.push(6) }
      sstmt!{ alice.account.balance = values[i] }
      sexpr!{ (alice.account.balance == 6) }
      (by change _ = true ∧ _ = true ∧ _ = true ∧ _ = true; decide) := by
  native_decide

/-! ## Storage push/pop unfolds

The `pushPlace` shape of `storageDeleteComplexTarget` (`delete
a.push()`) is not validated: it is not constructible from Solidity
source. -/

theorem storagePushValueUnfoldLeftFstReceiver_valid :
    Validates .storagePushValueUnfoldLeftFstReceiver
      sblock!{ uint i = 0; uint amount = 7; matrix.push() }
      sstmt!{ matrix[i].push(amount) }
      sexpr!{ (matrix[i][0] == 7) }
      (by change _ = Kind.storage ∧ _ = true ∧ _ = true; decide) := by
  native_decide

theorem storagePushValueUnfoldRightSndArgument_valid :
    Validates .storagePushValueUnfoldRightSndArgument
      sblock!{ uint amount = 7 }
      sstmt!{ values.push(amount + 1) }
      sexpr!{ (values[0] == 8) }
      (by change _ = Kind.storage ∧ _ = true ∧ _ = true; decide) := by
  native_decide

theorem storagePushUnfoldLeftFstReceiver_valid :
    Validates .storagePushUnfoldLeftFstReceiver
      sblock!{ uint i = 0; matrix.push() }
      sstmt!{ matrix[i].push() }
      sexpr!{ (matrix[i][0] == 0) }
      (by change _ = Kind.storage ∧ _ = true ∧ _ = none
          exact ⟨rfl, rfl, rfl⟩) := by
  native_decide

theorem storagePushLhsToPushValue_valid :
    Validates .storagePushLhsToPushValue
      sblock!{ uint amount = 7 }
      sstmt!{ values.push() = amount }
      sexpr!{ (values[0] == 7) }
      (by change _ = Kind.storage ∧ _ = true; decide) := by
  native_decide

theorem storageLocalRootPushUnfoldLeftFstReceiver_valid :
    Validates .storageLocalRootPushUnfoldLeftFstReceiver
      sblock!{ uint i = 0; matrix.push() }
      sstmt!{ p = matrix[i].push() }
      sexpr!{ (p == 0) }
      (by change _ = Kind.storage ∧ _ = true ∧ ¬ (_ = Kind.memory ∧ _ = true)
          decide) := by
  native_decide

theorem storagePopUnfoldLeftFstReceiver_valid :
    Validates .storagePopUnfoldLeftFstReceiver
      sblock!{ uint i = 0; matrix.push(); matrix[i].push(3); matrix[i].push(4) }
      sstmt!{ matrix[i].pop() }
      sexpr!{ (matrix[i][0] == 3) }
      (by change _ = Kind.storage ∧ _ = true; decide) := by
  native_decide

/-! ## Memory write/read unfolds -/

theorem memoryWriteUnfoldRightSndResult_valid :
    Validates .memoryWriteUnfoldRightSndResult
      sblock!{ Person memory carol; bob.age = 4 }
      sstmt!{ carol.age = bob.age }
      sexpr!{ (carol.age == 4) }
      (by change _ = Kind.memory ∧ _ = true ∧ _ = true ∧ True
          exact ⟨rfl, rfl, rfl, trivial⟩) := by
  native_decide

theorem memoryFieldWriteUnfoldLeftFst_valid :
    Validates .memoryFieldWriteUnfoldLeftFst
      sblock!{ Person memory carol; uint amount = 7 }
      sstmt!{ carol.account.balance = amount }
      sexpr!{ (carol.account.balance == 7) }
      (by change _ = true ∧ _ = true; decide) := by
  native_decide

theorem memoryLocalDeclInitDrop_valid :
    Validates .memoryLocalDeclInitDrop
      sblock!{ Person memory carol; carol.age = 3 }
      sstmt!{ Person memory david = carol }
      sexpr!{ (david.age == 3) }
      (by change _ = true; decide) := by
  native_decide

theorem memoryFieldReadUnfoldRightFst_valid :
    Validates .memoryFieldReadUnfoldRightFst
      sblock!{ Person memory carol; carol.account.balance = 5; uint amount = 0 }
      sstmt!{ amount = carol.account.balance }
      sexpr!{ (amount == 5) }
      (by change _ = true ∧ ¬ _ = true; decide) := by
  native_decide

theorem memoryFieldReadUnfoldRightSndResult_valid :
    Validates .memoryFieldReadUnfoldRightSndResult
      sblock!{ Person memory carol; Person memory david;
               david.account.balance = 6 }
      sstmt!{ carol.account = david.account }
      sexpr!{ (carol.account.balance == 6) }
      (by change _ = true ∧ _ = true ∧ _ = true; decide) := by
  native_decide

/-- Primitive-typed instance: the `pv` capture must be a stack
declaration (`Rules.valueCaptureKind`). -/
theorem memoryFieldReadUnfoldRightSndResult_primitive_valid :
    Validates .memoryFieldReadUnfoldRightSndResult
      sblock!{ Person memory carol; Person memory david; david.age = 6 }
      sstmt!{ carol.account.balance = david.age }
      sexpr!{ (carol.account.balance == 6) }
      (by change _ = true ∧ _ = true ∧ _ = true; decide) := by
  native_decide

/-! ## Memory delete unfolds -/

theorem memoryDeleteComplexTarget_field_valid :
    Validates .memoryDeleteComplexTarget
      sblock!{ Person memory carol; carol.account.balance = 5 }
      sstmt!{ delete carol.account.balance }
      sexpr!{ (carol.account.balance == 0) }
      (by change _ = true; decide) := by
  native_decide

theorem memoryDeleteComplexTarget_index_valid :
    Validates .memoryDeleteComplexTarget
      (sblock!{ uint i = 0; values.push(1); values.push(2) } ++ [mrowDecl])
      (Stmt.delete (indexPlace mrow (sexpr!{ i + 1 })))
      (eqE (indexExpr mrow (lit 1)) (lit 0))
      (by change _ = true ∨ (_ = true ∧ _ = true); decide) := by
  native_decide

/-! ## Memory indexed write/read unfolds -/

theorem memoryIndexWriteUnfoldLeftFst_valid :
    Validates .memoryIndexWriteUnfoldLeftFst
      (sblock!{ uint i = 0; uint amount = 7; matrix.push();
                matrix[i].push(3) } ++ [mmDecl])
      (Stmt.assign (indexPlace (indexExpr mm iE) iE) amountE)
      (eqE (indexExpr (indexExpr mm iE) iE) (lit 7))
      (by change _ = true ∧ _ = true; decide) := by
  native_decide

theorem memoryIndexWriteUnfoldLeftSndIndex_valid :
    Validates .memoryIndexWriteUnfoldLeftSndIndex
      (sblock!{ uint i = 0; uint amount = 7; values.push(1);
                values.push(2) } ++ [mrowDecl])
      (Stmt.assign (indexPlace mrow (sexpr!{ i + 1 })) amountE)
      (eqE (indexExpr mrow (lit 1)) (lit 7))
      (by change _ = true ∧ _ = true ∧ _ = true; decide) := by
  native_decide

theorem memoryIndexReadUnfoldRightFst_valid :
    Validates .memoryIndexReadUnfoldRightFst
      (sblock!{ uint i = 0; uint amount = 0; matrix.push();
                matrix[i].push(3) } ++ [mmDecl])
      (Stmt.assign (splace!{ amount }) (indexExpr (indexExpr mm iE) iE))
      sexpr!{ (amount == 3) }
      (by change _ = true ∧ ¬ _ = true; decide) := by
  native_decide

theorem memoryIndexReadUnfoldRightSndIndex_valid :
    Validates .memoryIndexReadUnfoldRightSndIndex
      (sblock!{ uint i = 0; uint amount = 0; values.push(1);
                values.push(2) } ++ [mrowDecl])
      (Stmt.assign (splace!{ amount }) (indexExpr mrow (sexpr!{ i + 1 })))
      sexpr!{ (amount == 2) }
      (by change _ = true ∧ _ = true ∧ ¬ _ = true; decide) := by
  native_decide

theorem memoryIndexReadUnfoldRightSndResult_valid :
    Validates .memoryIndexReadUnfoldRightSndResult
      (sblock!{ uint i = 0; people.push(); people[i].age = 5;
                Person memory carol } ++ [psDecl])
      (Stmt.assign (fieldPlace (rootExpr "carol") "account") (indexExpr ps iE))
      sexpr!{ (carol.account.age == 5) }
      (by change _ = true ∧ _ = true ∧ _ = true ∧ _ = true; decide) := by
  native_decide

/-! ## Cross-domain unfolds -/

theorem storageToMemoryDeclUnfoldRightFst_valid :
    Validates .storageToMemoryDeclUnfoldRightFst
      sblock!{ alice.account.token.value = 9 }
      (Stmt.memoryDecl StandardExample.tokenTy "mtok2"
        (some (sexpr!{ alice.account.token })))
      (eqE (fieldExpr mtok2 "value") (lit 9))
      (by change _ = true; decide) := by
  native_decide

/-- `Account memory macc;` target for `memoryStorageCopyUnfold`. -/
def macc : WrappedExpr := varExpr Kind.memory StandardExample.accountTy "macc"
def maccDecl : Stmt := Stmt.memoryDecl StandardExample.accountTy "macc" none

/-- `macc = alice.account;` — complex storage RHS into a memory root is
captured into a storage alias first (KeY `memoryStorageCopyUnfold`). -/
theorem memoryStorageCopyUnfold_field_valid :
    Validates .memoryStorageCopyUnfold
      (sblock!{ alice.account.balance = 7 } ++ [maccDecl])
      (Stmt.assign (varPlace Kind.memory StandardExample.accountTy "macc")
        (sexpr!{ alice.account }))
      (eqE (fieldExpr macc "balance") (lit 7))
      (by change _ = Kind.memory ∧ _ = true ∧ _ = true; decide) := by
  native_decide

/-- `carol = people[i];` — indexed storage RHS into a memory root (KeY
`memoryStorageCopyUnfold`). -/
theorem memoryStorageCopyUnfold_index_valid :
    Validates .memoryStorageCopyUnfold
      sblock!{ uint i = 0; people.push(); people[i].age = 5;
               Person memory carol }
      sstmt!{ carol = people[i] }
      sexpr!{ (carol.age == 5) }
      (by change _ = Kind.memory ∧ _ = true ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem memoryToStorageUnfoldRightFstSource_valid :
    Validates .memoryToStorageUnfoldRightFstSource
      sblock!{ Person memory carol; carol.account.balance = 8 }
      sstmt!{ alice.account = carol.account }
      sexpr!{ (alice.account.balance == 8) }
      (by change _ = Kind.storage ∧ _ = true ∧ _ = true; decide) := by
  native_decide

/-- Primitive-typed instance of the cross-domain source capture
(`Rules.valueCaptureKind`). -/
theorem memoryToStorageUnfoldRightFstSource_primitive_valid :
    Validates .memoryToStorageUnfoldRightFstSource
      sblock!{ Person memory carol; carol.age = 3 }
      sstmt!{ alice.age = carol.age }
      sexpr!{ (alice.age == 3) }
      (by change _ = Kind.storage ∧ _ = true ∧ _ = true; decide) := by
  native_decide

theorem memoryToStorageUnfoldLeftFstTarget_valid :
    Validates .memoryToStorageUnfoldLeftFstTarget
      [mtokDecl, Stmt.assign (fieldPlace mtok "value") (lit 9)]
      (Stmt.assign (fieldPlace (sexpr!{ alice.account }) "token") mtok)
      sexpr!{ (alice.account.token.value == 9) }
      (by change _ = true ∧ _ = true ∧ _ = true; decide) := by
  native_decide

theorem memoryToStorageUnfoldLeftSndTargetIndex_valid :
    Validates .memoryToStorageUnfoldLeftSndTargetIndex
      sblock!{ uint i = 0; persons.push(); persons.push();
               Person memory carol; carol.age = 3 }
      sstmt!{ persons[i + 1] = carol }
      sexpr!{ (persons[1].age == 3) }
      (by change _ = true ∧ _ = true ∧ _ = true ∧ _ = true; decide) := by
  native_decide

/-! ## Value declarations and operators -/

theorem localValueDeclInitDrop_valid :
    Validates .localValueDeclInitDrop
      sblock!{ uint amount = 7 }
      sstmt!{ uint z = amount + 1 }
      sexpr!{ (z == 8) }
      (by change _ = true; decide) := by
  native_decide

theorem binopUnfoldLeft_add_valid :
    Validates (.binopUnfoldLeft .add)
      sblock!{ alice.age = 4; uint amount = 7; uint result }
      sstmt!{ result = alice.age + amount }
      sexpr!{ (result == 11) }
      (by change _ = _ ∧ (_ = true ∧ _ = true) ∧ _ = true; decide) := by
  native_decide

theorem binopUnfoldLeft_div_valid :
    Validates (.binopUnfoldLeft .div)
      sblock!{ alice.age = 42; uint amount = 7; uint result }
      sstmt!{ result = alice.age / amount }
      sexpr!{ (result == 6) }
      (by change _ = _ ∧ (_ = true ∧ _ = true) ∧ _ = true; decide) := by
  native_decide

theorem binopUnfoldLeft_lt_valid :
    Validates (.binopUnfoldLeft .lt)
      sblock!{ alice.age = 4; uint amount = 7; bool flag }
      sstmt!{ flag = (alice.age < amount) }
      sexpr!{ flag }
      (by change _ = _ ∧ (_ = true ∧ _ = true) ∧ _ = true; decide) := by
  native_decide

theorem binopUnfoldLeft_and_valid :
    Validates (.binopUnfoldLeft .and)
      sblock!{ alice.age = 4; bool flag; bool flag2 = true }
      sstmt!{ flag = (alice.age == 4) && flag2 }
      sexpr!{ flag }
      (by change _ = _ ∧ (_ = true ∧ _ = true) ∧ _ = true; decide) := by
  native_decide

theorem binopUnfoldLeft_or_valid :
    Validates (.binopUnfoldLeft .or)
      sblock!{ alice.age = 4; bool flag; bool flag2 }
      sstmt!{ flag = (alice.age == 4) || flag2 }
      sexpr!{ flag }
      (by change _ = _ ∧ (_ = true ∧ _ = true) ∧ _ = true; decide) := by
  native_decide

theorem logicalAndShortCircuitRhs_valid :
    Validates .logicalAndShortCircuitRhs
      sblock!{ alice.age = 4; bool flag2 = true; bool flag }
      sstmt!{ flag = flag2 && (alice.age == 4) }
      sexpr!{ flag }
      (by change _ = _ ∧ (_ = true ∧ _ = true) ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

/-- Short-circuit is real: the false left operand skips the reverting
`1 / 0` on the right (`x` stays 0, so `age / x` would revert). -/
theorem logicalAndShortCircuitRhs_shortCircuits_valid :
    Validates .logicalAndShortCircuitRhs
      sblock!{ alice.age = 4; uint x; bool flag2; bool flag = true }
      sstmt!{ flag = flag2 && ((alice.age / x) == 0) }
      sexpr!{ (flag == false) }
      (by change _ = _ ∧ (_ = true ∧ _ = true) ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem logicalOrShortCircuitRhs_valid :
    Validates .logicalOrShortCircuitRhs
      sblock!{ alice.age = 4; bool flag2; bool flag }
      sstmt!{ flag = flag2 || (alice.age == 4) }
      sexpr!{ flag }
      (by change _ = _ ∧ (_ = true ∧ _ = true) ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

/-- The true left operand skips the reverting right-hand side. -/
theorem logicalOrShortCircuitRhs_shortCircuits_valid :
    Validates .logicalOrShortCircuitRhs
      sblock!{ alice.age = 4; uint x; bool flag2 = true; bool flag }
      sstmt!{ flag = flag2 || ((alice.age / x) == 0) }
      sexpr!{ flag }
      (by change _ = _ ∧ (_ = true ∧ _ = true) ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem binopUnfoldRight_add_valid :
    Validates (.binopUnfoldRight .add)
      sblock!{ alice.age = 4; uint amount = 7; uint result }
      sstmt!{ result = amount + alice.age }
      sexpr!{ (result == 11) }
      (by change _ = _ ∧ _ = false ∧ (_ = true ∧ _ = true) ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem binopUnfoldRight_div_valid :
    Validates (.binopUnfoldRight .div)
      sblock!{ alice.age = 7; uint amount = 42; uint result }
      sstmt!{ result = amount / alice.age }
      sexpr!{ (result == 6) }
      (by change _ = _ ∧ _ = false ∧ (_ = true ∧ _ = true) ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem binopUnfoldRight_eqB_valid :
    Validates (.binopUnfoldRight .eqB)
      sblock!{ alice.age = 7; uint amount = 7; bool flag }
      sstmt!{ flag = (amount == alice.age) }
      sexpr!{ flag }
      (by change _ = _ ∧ _ = false ∧ (_ = true ∧ _ = true) ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem binopUnfoldResult_add_valid :
    Validates (.binopUnfoldResult .add)
      sblock!{ uint amount = 7 }
      sstmt!{ total = amount + amount }
      sexpr!{ (total == 14) }
      (by change _ = _ ∧ _ = true ∧ _ = true ∧ _ = true ∧
            ¬ (_ = true ∧ _ = true) ∧ ¬ (_ = Kind.memory ∧ _ = true)
          decide) := by
  native_decide

theorem binopUnfoldResult_pow_valid :
    Validates (.binopUnfoldResult .pow)
      sblock!{ uint amount = 7 }
      sstmt!{ total = amount ** 2 }
      sexpr!{ (total == 49) }
      (by change _ = _ ∧ _ = true ∧ _ = true ∧ _ = true ∧
            ¬ (_ = true ∧ _ = true) ∧ ¬ (_ = Kind.memory ∧ _ = true)
          decide) := by
  native_decide

theorem binopUnfoldResult_div_revert_cond :
    (ruleEffect (.binopUnfoldResult .div)).cond
      sstmt!{ total = amount / zero } := by
  change _ = _ ∧ _ = true ∧ _ = true ∧ _ = true ∧
    ¬ (_ = true ∧ _ = true) ∧ ¬ (_ = Kind.memory ∧ _ = true)
  decide

/-- Revert agreement: a zero divisor makes both the original statement
and the residual block revert.  The box entry uses the postcondition
`false`, which a *successful* run can never establish: `check` is `true`
under box only on a revert (a stuck run is `false`), so this entry holds
iff both sides revert.  (With post `true` the entry would also hold if
both sides succeeded — it would not test the revert at all.) -/
theorem binopUnfoldResult_div_revert_valid :
    Validates (.binopUnfoldResult .div)
      sblock!{ uint amount = 7; uint zero = 0 }
      sstmt!{ total = amount / zero }
      sexpr!{ false }
      binopUnfoldResult_div_revert_cond
      (sm := .box) := by
  native_decide

/-- The diamond twins fail on both sides, confirming the revert (a
diamond judgment with post `true` holds exactly when the run succeeds). -/
theorem binopUnfoldResult_div_revert_not_diamond :
    ¬ validated .diamond
        (sblock!{ uint amount = 7; uint zero = 0 } ++
          [sstmt!{ total = amount / zero }])
        sexpr!{ true } ∧
    ¬ validated .diamond
        (sblock!{ uint amount = 7; uint zero = 0 } ++
          (ruleEffect (.binopUnfoldResult .div)).block
            sstmt!{ total = amount / zero }
            binopUnfoldResult_div_revert_cond)
        sexpr!{ true } := by
  constructor <;> native_decide

theorem unopCapture_neg_valid :
    Validates (.unopCapture .neg)
      sblock!{ alice.age = 4; uint x = 0 }
      sstmt!{ x = -alice.age }
      sexpr!{ (x == -4) }
      (by change _ = _ ∧ (_ = true ∧ _ = true) ∧ _ = true; decide) := by
  native_decide

theorem unopCapture_not_valid :
    Validates (.unopCapture .not)
      sblock!{ alice.age = 5; bool flag }
      sstmt!{ flag = !(alice.age == 4) }
      sexpr!{ flag }
      (by change _ = _ ∧ (_ = true ∧ _ = true) ∧ _ = true; decide) := by
  native_decide

/-! ## Compound-assignment and inc/dec unfolds -/

theorem storageFieldCompoundAssignUnfoldLeftFst_add_valid :
    Validates (.storageFieldCompoundAssignUnfoldLeftFst .add)
      sblock!{ alice.account.balance = 5; uint amount = 7 }
      sstmt!{ alice.account.balance += amount }
      sexpr!{ (alice.account.balance == 12) }
      (by change _ = _ ∧ _ = true ∧ _ = true ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem storageFieldCompoundAssignUnfoldLeftFst_div_valid :
    Validates (.storageFieldCompoundAssignUnfoldLeftFst .div)
      sblock!{ alice.account.balance = 14; uint amount = 7 }
      sstmt!{ alice.account.balance /= amount }
      sexpr!{ (alice.account.balance == 2) }
      (by change _ = _ ∧ _ = true ∧ _ = true ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem storageIndexCompoundAssignUnfoldLeftFst_add_valid :
    Validates (.storageIndexCompoundAssignUnfoldLeftFst .add)
      sblock!{ uint i = 0; uint amount = 7; matrix.push(); matrix[i].push(3) }
      sstmt!{ matrix[i][i] += amount }
      sexpr!{ (matrix[i][i] == 10) }
      (by change _ = _ ∧ _ = true ∧ _ = true ∧ _ = true ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem storageFieldIncDecUnfoldLeftFst_preInc_valid :
    Validates (.storageFieldIncDecUnfoldLeftFst .preInc)
      sblock!{ alice.account.balance = 5 }
      sstmt!{ ++alice.account.balance }
      sexpr!{ (alice.account.balance == 6) }
      (by change _ = _ ∧ _ = true; decide) := by
  native_decide

theorem storageFieldIncDecUnfoldLeftFst_postDec_valid :
    Validates (.storageFieldIncDecUnfoldLeftFst .postDec)
      sblock!{ alice.account.balance = 5 }
      (Stmt.expr (incDecExpr .postDec (sexpr!{ alice.account.balance })))
      sexpr!{ (alice.account.balance == 4) }
      (by change _ = _ ∧ _ = true; decide) := by
  native_decide

theorem storageIndexIncDecUnfoldLeftFst_preInc_valid :
    Validates (.storageIndexIncDecUnfoldLeftFst .preInc)
      sblock!{ uint i = 0; matrix.push(); matrix[i].push(3) }
      sstmt!{ ++matrix[i][i] }
      sexpr!{ (matrix[i][i] == 4) }
      (by change _ = _ ∧ _ = true ∧ _ = true; decide) := by
  native_decide

/-! ### Memory targets

The calculus's memory-target arithmetic (`memoryFieldOpAssign`,
`memoryFieldDivAssign`, `memoryIndexArrayOpAssign`, `memoryFieldIncrement`;
solkey `444f029579`).  Only the *unfold* twins need a `Validates` entry: the
terminal forms have empty residuals and their content is the update theorems
in `Wp/Terminal/UpdateCompound.lean`.  `carol.account` is a complex
memory path, so the field form unfolds; `mm[i]` is a complex memory array
path for the index form. -/

theorem memoryFieldCompoundAssignUnfoldLeftFst_add_valid :
    Validates (.memoryFieldCompoundAssignUnfoldLeftFst .add)
      sblock!{ Person memory carol; carol.account.balance = 5; uint amount = 7 }
      sstmt!{ carol.account.balance += amount }
      sexpr!{ (carol.account.balance == 12) }
      (by change _ = _ ∧ _ = true ∧ _ = true ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem memoryFieldCompoundAssignUnfoldLeftFst_div_valid :
    Validates (.memoryFieldCompoundAssignUnfoldLeftFst .div)
      sblock!{ Person memory carol; carol.account.balance = 14; uint amount = 7 }
      sstmt!{ carol.account.balance /= amount }
      sexpr!{ (carol.account.balance == 2) }
      (by change _ = _ ∧ _ = true ∧ _ = true ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem memoryIndexCompoundAssignUnfoldLeftFst_add_valid :
    Validates (.memoryIndexCompoundAssignUnfoldLeftFst .add)
      (sblock!{ uint i = 0; uint amount = 7; matrix.push();
                matrix[i].push(3) } ++ [mmDecl])
      (Stmt.compoundAssign .add (indexPlace (indexExpr mm iE) iE) amountE)
      (eqE (indexExpr (indexExpr mm iE) iE) (lit 10))
      (by change _ = _ ∧ _ = true ∧ _ = true ∧ _ = true ∧ _ = true ∧ _ = true
          decide) := by
  native_decide

theorem memoryFieldIncDecUnfoldLeftFst_preInc_valid :
    Validates (.memoryFieldIncDecUnfoldLeftFst .preInc)
      sblock!{ Person memory carol; carol.account.balance = 5 }
      sstmt!{ ++carol.account.balance }
      sexpr!{ (carol.account.balance == 6) }
      (by change _ = _ ∧ _ = true; decide) := by
  native_decide

theorem memoryFieldIncDecUnfoldLeftFst_postDec_valid :
    Validates (.memoryFieldIncDecUnfoldLeftFst .postDec)
      sblock!{ Person memory carol; carol.account.balance = 5 }
      (Stmt.expr (incDecExpr .postDec (sexpr!{ carol.account.balance })))
      sexpr!{ (carol.account.balance == 4) }
      (by change _ = _ ∧ _ = true; decide) := by
  native_decide

theorem memoryIndexIncDecUnfoldLeftFst_preInc_valid :
    Validates (.memoryIndexIncDecUnfoldLeftFst .preInc)
      (sblock!{ uint i = 0; matrix.push(); matrix[i].push(3) } ++ [mmDecl])
      (Stmt.expr (incDecExpr .preInc (indexExpr (indexExpr mm iE) iE)))
      (eqE (indexExpr (indexExpr mm iE) iE) (lit 4))
      (by change _ = _ ∧ _ = true ∧ _ = true; decide) := by
  native_decide

theorem compoundAssignValueRhsCapture_add_valid :
    Validates (.compoundAssignValueRhsCapture .add)
      sblock!{ uint amount = 2; bob.age = 3 }
      sstmt!{ amount += bob.age + 1 }
      sexpr!{ (amount == 6) }
      (by change _ = _ ∧ _ = true ∧ ¬ (_ = true ∧ _ = true); decide) := by
  native_decide

/-- Storage-target instance of the location-neutral capture (KeY
`addAssignValueRhsCapture` with a storage lhs): the storage read on the
RHS is hoisted first. -/
theorem compoundAssignValueRhsCapture_storage_valid :
    Validates (.compoundAssignValueRhsCapture .add)
      sblock!{ age = 5; bob.age = 3 }
      sstmt!{ age += bob.age }
      sexpr!{ (age == 8) }
      (by change _ = _ ∧ _ = true ∧ ¬ (_ = true ∧ _ = true); decide) := by
  native_decide

/-! ## Ternary lowering (KeY `ternaryCaptureCond`/`ternaryToIf`) -/

theorem ternaryCaptureCond_valid :
    Validates .ternaryCaptureCond
      sblock!{ bob.age = 3; uint amount = 0 }
      sstmt!{ amount = (bob.age > 2) ? 10 : 20 }
      sexpr!{ (amount == 10) }
      (by change _ = true ∧ ¬ (_ = Kind.memory ∧ _ = true); decide) := by
  native_decide

theorem ternaryToIf_valid :
    Validates .ternaryToIf
      sblock!{ bool flag = true; uint amount = 0 }
      sstmt!{ amount = flag ? 10 : 20 }
      sexpr!{ (amount == 10) }
      (by change _ = true ∧ _ = true ∧ _ = true; decide) := by
  native_decide

theorem ternaryToIfStorage_valid :
    Validates .ternaryToIfStorage
      sblock!{ bool flag = false }
      sstmt!{ age = flag ? 10 : 20 }
      sexpr!{ (age == 20) }
      (by change _ = true ∧ _ = true; decide) := by
  native_decide

/-! ## `*ValueRhsCapture` trio (evaluation-order captures) -/

/-- `total = i++;` — inc/dec RHS into a global root (KeY
`storageRootWriteValueRhsCapture`). -/
theorem storageRootWriteValueRhsCapture_valid :
    Validates .storageRootWriteValueRhsCapture
      sblock!{ uint i = 3 }
      sstmt!{ total = i++ }
      sexpr!{ (total == 3) }
      (by exact ⟨by change _ = true; decide, trivial⟩) := by
  native_decide

/-- `alice.age = i++;` — inc/dec RHS into a storage field (KeY
`fieldWriteValueRhsCapture`). -/
theorem fieldWriteValueRhsCapture_valid :
    Validates .fieldWriteValueRhsCapture
      sblock!{ uint i = 3 }
      sstmt!{ alice.age = i++ }
      sexpr!{ (alice.age == 3) }
      (by exact trivial) := by
  native_decide

/-- `values[k] = i++;` — inc/dec RHS into a storage array slot (KeY
`indexWriteValueRhsCapture`). -/
theorem indexWriteValueRhsCapture_valid :
    Validates .indexWriteValueRhsCapture
      sblock!{ values.push(9); uint k = 0; uint i = 3 }
      sstmt!{ values[k] = i++ }
      sexpr!{ (values[k] == 3) }
      (by exact trivial) := by
  native_decide

/-- `total = i + j * k;` — a binop with a complex operand is not
`binopUnfoldResult`'s cell; the capture fires instead. -/
theorem storageRootWriteValueRhsCapture_binop_valid :
    Validates .storageRootWriteValueRhsCapture
      sblock!{ uint i = 3; uint j = 4; uint k = 5 }
      sstmt!{ total = i + j * k }
      sexpr!{ (total == 23) }
      (by exact ⟨by change _ = true; decide,
        fun h => absurd h.2.2 (by change ¬ _ = true; decide)⟩) := by
  native_decide

/-! ## Rule correspondence lock-ins (`docs/lean-key-rule-map.md`)

Concrete find-shapes of KeY taclets whose Lean coverage is a *merged*
rule or a rule chain, locking the correspondence in by evaluation. -/

/-- KeY `storageIndexWriteStorageRefRhsCapture` (solidityProgramRules.key
`sp[e] = nsp;` with a complex storage-reference RHS): merged into
`storageIndexReadUnfoldRightSndResult`. -/
theorem storageIndexWriteStorageRefRhsCapture_corresp :
    Validates .storageIndexReadUnfoldRightSndResult
      sblock!{ uint i = 0; uint j = 1; matrix.push(); matrix.push();
               matrix[j].push(5) }
      sstmt!{ matrix[i] = matrix[j] }
      sexpr!{ (matrix[i][0] == 5) }
      (by change _ = true ∧ _ = true ∧ _ = true ∧ _ = true; decide) := by
  native_decide

/-- KeY `storageIndexWriteRootRhsNonSimpleIndexCapture`
(`gp[nse] = sp;` — simple storage-root RHS, complex index): merged into
`storageIndexWriteUnfoldLeftSndIndex`, whose condition does not
distinguish stack from storage simple RHSs. -/
theorem storageIndexWriteRootRhsNonSimpleIndexCapture_corresp :
    Validates .storageIndexWriteUnfoldLeftSndIndex
      sblock!{ uint i = 0; people.push(); people.push(); bob.age = 4 }
      sstmt!{ people[i + 1] = bob }
      sexpr!{ (people[1].age == 4) }
      (by change _ = true ∧ _ = true ∧ _ = true ∧ ¬ _ = true; decide) := by
  native_decide

/-- KeY `storagePushValueCopySource_unfold_leftFstReceiver`: the
receiver unfold also admits a storage-path payload (copy-source
flavor); Lean merges it into `storagePushValueUnfoldLeftFstReceiver`
(rule-map `verify` row resolved). -/
theorem storagePushValueCopySource_unfold_leftFstReceiver_corresp :
    Validates .storagePushValueUnfoldLeftFstReceiver
      sblock!{ uint i = 0; matrix.push(); alice.age = 9 }
      sstmt!{ matrix[i].push(alice.age) }
      sexpr!{ (matrix[i][0] == 9) }
      (by change _ = Kind.storage ∧ _ = true ∧ _ = true; decide) := by
  native_decide

/-! ### Evaluation order (KeY `testStorageEvaluationOrder`)

KeY — like solc, in both the legacy and the IR pipeline — evaluates
the RHS of an assignment *before* the target's index (`a[++i] = ++i`
with `i = 0` ends with `a[2] == 1`). The Lean rewrite layer implements
that order (the dispatcher tests `rhs.simple` first, so
`indexWriteValueRhsCapture` hoists the RHS before the index capture
fires), and since `execAssign` reads the RHS before resolving the
target the interpreter agrees. Both layers are locked to the KeY/solc
outcome below. -/

/-- `values[++i] = ++i;` -/
def evalOrderStmt : Stmt :=
  Stmt.assign (indexPlace (rootExpr "values") (incDecExpr .preInc iE))
    (incDecExpr .preInc iE)

def evalOrderSetup : Block :=
  sblock!{ uint i = 0; values.push(100); values.push(100);
           values.push(100) }

/-- The interpreter is RHS-first, as in KeY and solc:
`values[2] == 1`. -/
theorem storageEvaluationOrder_interpreter_rhsFirst :
    validated .diamond (evalOrderSetup ++ [evalOrderStmt])
      sexpr!{ (values[2] == 1) } := by
  native_decide

/-- The rewrite layer computes the same order: after
`indexWriteValueRhsCapture`, the residual yields `values[2] == 1` —
the KeY `testStorageEvaluationOrder` outcome. -/
theorem storageEvaluationOrder_rewrite_rhsFirst :
    validated .diamond
      (evalOrderSetup ++
        (ruleEffect .indexWriteValueRhsCapture).block evalOrderStmt
          (by exact trivial))
      sexpr!{ (values[2] == 1) } := by
  native_decide

/-! ## Function calls (inlined semantics)

`check` is stuck on `Stmt.callStmt`, so call rules are validated
against `SolidityJudgment.checkInlined` (inline through
`SoliditySyntax.funDef`, then `check`). -/

abbrev validatedInlined (sm : SolidityModality) (blk : Block)
    (post : WrappedExpr) : Prop :=
  (SolidityJudgment.mk ⟨sm, blk⟩ post).checkInlined = true

/-- `result = addOne(4);` -/
def addOneCall : Stmt :=
  Stmt.callStmt (some (rootPlace "result")) "addOne" [intLitExpr 4]

/-- KeY `functionBodyExpand`: the original call (inlined) and the
rule's residual (call-free, plain `check`) validate the same post. -/
theorem functionBodyExpand_valid :
    validatedInlined .diamond [addOneCall] sexpr!{ (result == 5) } ∧
      validated .diamond
        ((ruleEffect .functionBodyExpand).block addOneCall
          (by exact ⟨by decide, by decide⟩))
        sexpr!{ (result == 5) } := by
  constructor <;> native_decide

/-- `result = addOne(alice.age);` — complex argument. -/
def addOneComplexCall : Stmt :=
  Stmt.callStmt (some (rootPlace "result")) "addOne" [sexpr!{ alice.age }]

/-- `functionCallArgCapture` (solkey's backlog `unfoldArgument` — not a
name the calculus declares; beyond
solkey): capture the complex argument, then expand. Both sides still
contain a call, so both go through `checkInlined`. -/
theorem functionCallArgCapture_valid :
    validatedInlined .diamond
      (sblock!{ alice.age = 4 } ++ [addOneComplexCall])
      sexpr!{ (result == 5) } ∧
      validatedInlined .diamond
        (sblock!{ alice.age = 4 } ++
          (ruleEffect .functionCallArgCapture).block addOneComplexCall
            (by change _ = true; decide))
        sexpr!{ (result == 5) } := by
  constructor <;> native_decide

/-! ## Assert, if-then-else, transfer -/

theorem assertConditionCapture_valid :
    Validates .assertConditionCapture
      sblock!{ alice.age = 4 }
      sstmt!{ assert((alice.age == 4)) }
      sexpr!{ (alice.age == 4) }
      (by change _ = true; decide) := by
  native_decide

theorem requireConditionCapture_valid :
    Validates .requireConditionCapture
      sblock!{ alice.age = 4 }
      sstmt!{ require((alice.age == 4)) }
      sexpr!{ (alice.age == 4) }
      (by change _ = true; decide) := by
  native_decide

/-! A passing `assert`/`require` has no observable effect, so the two
entries above only show that neither side reverts or sticks — a residual
that dropped the check would pass them too.  The discriminating entries
are the *violated* ones: box modality with postcondition `false` holds
iff both sides revert (see `binopUnfoldResult_div_revert_valid`). -/

theorem assertConditionCapture_violated_valid :
    Validates .assertConditionCapture
      sblock!{ alice.age = 4 }
      sstmt!{ assert((alice.age == 5)) }
      sexpr!{ false }
      (by change _ = true; decide)
      (sm := .box) := by
  native_decide

theorem requireConditionCapture_violated_valid :
    Validates .requireConditionCapture
      sblock!{ alice.age = 4 }
      sstmt!{ require((alice.age == 5)) }
      sexpr!{ false }
      (by change _ = true; decide)
      (sm := .box) := by
  native_decide

theorem ifElseUnfold_valid :
    Validates .ifElseUnfold
      sblock!{ alice.age = 4 }
      sstmt!{ if ((alice.age == 4)) { total = 1 } else { total = 2 } }
      sexpr!{ (total == 1) }
      (by change _ = true ∧ _
          exact ⟨rfl, fun _ h => nomatch h⟩) := by
  native_decide

theorem ifElseTrue_valid :
    Validates .ifElseTrue
      ([] : Block)
      sstmt!{ if (true) { total = 1 } else { total = 2 } }
      sexpr!{ (total == 1) }
      trivial := by
  native_decide

theorem ifElseFalse_valid :
    Validates .ifElseFalse
      ([] : Block)
      sstmt!{ if (false) { total = 1 } else { total = 2 } }
      sexpr!{ (total == 2) }
      trivial := by
  native_decide

theorem ifElseNegated_valid :
    Validates .ifElseNegated
      sblock!{ bool flag }
      sstmt!{ if (!flag) { total = 1 } else { total = 2 } }
      sexpr!{ (total == 1) }
      (by change _ = true; decide) := by
  native_decide

theorem transferUnfoldLeftFstReceiver_valid :
    Validates .transferUnfoldLeftFstReceiver
      sblock!{ bob.age = 2; uint amount = 7 }
      sstmt!{ bob.age.transfer(amount) }
      sexpr!{ (net(2) == -7) }
      (by change _ = true; decide) := by
  native_decide

theorem transferUnfoldRightSndArgument_valid :
    Validates .transferUnfoldRightSndArgument
      sblock!{ uint to = 2; uint amount = 7 }
      sstmt!{ to.transfer(amount + 1) }
      sexpr!{ (net(2) == -8) }
      (by change _ = true ∧ _ = true; decide) := by
  native_decide

end RuleValidation
end Solidity
