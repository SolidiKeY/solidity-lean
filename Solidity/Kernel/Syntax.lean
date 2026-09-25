import Solidity.Kernel.Contract
import Solidity.Typing.State

/-!
# Typed syntax

Phase 2 of `docs/kernel-port.md`, after mini-solkey's `Ch02_Elab`: the
statement forms of the calculus as an indexed family, so that the checks
`Semantics.stmtWt` makes at run time are made by the types instead.  This
file is the **storage slice**: storage paths, value expressions over the
stack and storage, declarations, assignment, `delete`, the branch and the
aborts.  Memory, arrays with `push`/`pop`, compound assignment and calls are
later slices (the tracker has the list).

Every family is indexed by the contract `C` and by the local context `Γ`
(`Semantics.Ctx`, the one `stmtWt` threads); a statement is a
`Stmt C Γ Γ'`, taking the context before it to the context after it.  A name
carries the proof of what it is bound to:

* a storage root `r` carries `C.rootType r = some T` **and**
  `lookupBy r Γ = none` — a local of the same name shadows it, exactly as
  `resolveS` looks in the environment first;
* a local carries its `Γ` binding, and a member access carries
  `C.fieldType s f = some T`.

What the types rule out, compared with what `stmtWt` accepts (each is a
`Coverage.ResidueShape` or the reason one is unreachable; the tracker records
the verdicts):

* a storage alias has a reference type, and a stack local a primitive one,
  so `sp = x` (`assignStorageLocalRootFromStack`) and a reference-typed stack
  source (`assignStackRefUnfoldTarget`) cannot be written;
* a member or index access has the location of its base, so the stack-kind
  field and index places `wtExpr` admits (`assignStackPlace`,
  `assignStackPlaceRhs`) do not exist;
* `delete` takes a `Loc`, never a bare alias (`deleteStorageLocalRoot`);
* an operator is applied at the primitive type it accepts
  (`assignOperatorRhsRefTyped`); a source is a `Val` at a primitive type or a
  storage path at a reference type, never a path at a primitive type, so the
  two readings of `x = alice.age` are one.
-/

namespace Solidity

/-! ## Operators at primitive types -/

/-- The primitive operand type an operator accepts: arithmetic and
comparisons on numbers, `&&`/`||` on booleans, `==`/`!=` on either. -/
def BinOp.accepts : BinOp → PrimTy → Bool
  | .and, p | .or, p => p == .bool
  | .eqB, _ | .neB, _ => true
  | _, p => p.isNumeric

/-- The result type at operand type `p`, as `BinOp.retTy` computes it. -/
def BinOp.ret (op : BinOp) (p : PrimTy) : PrimTy :=
  if op.isArith then p else .bool

/-- `a + b` on `uint` is a `uint`, `a < b` a `bool`. -/
theorem BinOp.retTy_prim (op : BinOp) (p : PrimTy) :
    op.retTy (.prim p) = .prim (op.ret p) := by
  unfold BinOp.retTy BinOp.ret; split <;> rfl

def UnOp.accepts : UnOp → PrimTy → Bool
  | .neg, p => p.isNumeric
  | .not, p => p == .bool

def UnOp.ret : UnOp → PrimTy → PrimTy
  | .neg, p => p
  | .not, _ => .bool

/-- `-x` keeps its type, `!b` is a `bool`. -/
theorem UnOp.retTy_prim (op : UnOp) (p : PrimTy) :
    op.retTy (.prim p) = .prim (op.ret p) := by
  cases op <;> rfl

namespace Kernel

open Semantics

/-! ## Paths and values -/

mutual

/-- A storage path of type `T`: an alias, or a location. -/
inductive SPath (C : Contract) (Γ : Ctx) : Ty → Type where
  /-- A local storage alias, `Person storage p = alice;` then `p`. -/
  | alias {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.path (.ref R))) :
      SPath C Γ (.ref R)
  | loc {T : Ty} (l : Loc C Γ T) : SPath C Γ T

/-- A storage location: what `delete` and a write reach through. -/
inductive Loc (C : Contract) (Γ : Ctx) : Ty → Type where
  /-- A state variable, `alice`. -/
  | root {T : Ty} (r : Name) (hΓ : lookupBy r Γ = none) (h : C.rootType r = some T) :
      Loc C Γ T
  /-- A member, `alice.age`. -/
  | field {s : Name} {T : Ty} (b : SPath C Γ (.struct s)) (f : Name)
      (h : C.fieldType s f = some T) : Loc C Γ T
  /-- A mapping entry, `balances[i]`. -/
  | mapIndex {k : PrimTy} {V : Ty} (b : SPath C Γ (.mapping (.prim k) V))
      (i : Val C Γ k) : Loc C Γ V
  /-- An array element, `values[i]`. -/
  | arrIndex {E : Ty} (b : SPath C Γ (.array E)) (i : Val C Γ .uint) : Loc C Γ E

/-- A value of primitive type `p`. -/
inductive Val (C : Contract) (Γ : Ctx) : PrimTy → Type where
  /-- A number literal, `10`. -/
  | lit {p : PrimTy} (n : Int) (h : p.isNumeric = true) : Val C Γ p
  /-- `true`, `false`. -/
  | bool (b : Bool) : Val C Γ .bool
  /-- A stack local, `uint x = 1;` then `x`. -/
  | local {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p))) :
      Val C Γ p
  /-- A storage read, `alice.age`. -/
  | read {p : PrimTy} (l : Loc C Γ (.prim p)) : Val C Γ p
  | binop {p : PrimTy} (op : BinOp) (h : op.accepts p = true) (a b : Val C Γ p) :
      Val C Γ (op.ret p)
  | unop {p : PrimTy} (op : UnOp) (h : op.accepts p = true) (a : Val C Γ p) :
      Val C Γ (op.ret p)

end

/-- The source of an assignment: a value at a primitive type, a storage path
(copied, or aliased) at a reference type. -/
inductive Src (C : Contract) (Γ : Ctx) : Ty → Type where
  | val {p : PrimTy} (v : Val C Γ p) : Src C Γ (.prim p)
  | path {R : RefTy} (p : SPath C Γ (.ref R)) : Src C Γ (.ref R)

/-! ## Statements -/

mutual

/-- A statement, from context `Γ` to context `Γ'`. -/
inductive Stmt (C : Contract) : Ctx → Ctx → Type where
  /-- `alice.age = 10;`, `alice = bob;`, `p = bob;` (an alias rebinds). -/
  | assign {Γ : Ctx} {T : Ty} (l : SPath C Γ T) (r : Src C Γ T) : Stmt C Γ Γ
  /-- `x = alice.age;` -/
  | assignLocal {Γ : Ctx} {p : PrimTy} (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim p))) (r : Val C Γ p) : Stmt C Γ Γ
  /-- `uint x;`, `uint x = e;` -/
  | declLocal {Γ : Ctx} (p : PrimTy) (x : Name) (init : Option (Val C Γ p)) :
      Stmt C Γ (setBy x (.stack (.prim p)) Γ)
  /-- `Person storage p = alice;` -/
  | declStorage {Γ : Ctx} (R : RefTy) (x : Name) (init : SPath C Γ (.ref R)) :
      Stmt C Γ (setBy x (.path (.ref R)) Γ)
  /-- `Person storage p;`, which binds nothing (`storageLocalDeclSkip`). -/
  | declStorageSkip {Γ : Ctx} (R : RefTy) (x : Name) : Stmt C Γ Γ
  /-- The calculus's own alias capture, `T storage sp = nsp;`: a
  `storagePlaceAlias`, which a program never writes. -/
  | bindAlias {Γ : Ctx} (R : RefTy) (x : Name) (init : SPath C Γ (.ref R)) :
      Stmt C Γ (setBy x (.path (.ref R)) Γ)
  /-- `delete alice.account;` -/
  | delete {Γ : Ctx} {T : Ty} (l : Loc C Γ T) : Stmt C Γ Γ
  /-- `if (c) { … } else { … }`; the branches declare nothing that
  survives them, as `stmtWt` requires. -/
  | ite {Γ : Ctx} (c : Val C Γ .bool) (thn els : Prog C Γ Γ) : Stmt C Γ Γ
  | require {Γ : Ctx} (c : Val C Γ .bool) : Stmt C Γ Γ
  | assert {Γ : Ctx} (c : Val C Γ .bool) : Stmt C Γ Γ
  | revert {Γ : Ctx} : Stmt C Γ Γ

/-- A block, threading the context through its statements. -/
inductive Prog (C : Contract) : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : Prog C Γ Γ
  | cons {Γ Γ₁ Γ₂ : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) : Prog C Γ Γ₂

end

end Kernel
end Solidity
