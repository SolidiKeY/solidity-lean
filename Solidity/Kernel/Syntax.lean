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
* a declaration introduces a fresh name, so a local never shadows another or
  a state variable, and the context only grows;
* a branch or a guard tests a simple condition (`Simple`), which is what
  `ifElseSplit`, `requireSimple` and `assertSimple` take;
* an operator is applied at the primitive type it accepts
  (`assignOperatorRhsRefTyped`); a source is a `Val` at a primitive type or a
  storage path at a reference type, never a path at a primitive type, so the
  two readings of `x = alice.age` are one;
* a storage write and an alias rebinding are different statements, and a
  copied type holds no mapping (the interpreter's `rhsToSVal` is stuck on one,
  and solc rejects the program).
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

/-- `x` is fresh at `Γ`: no local and no state variable is called `x`.  A
declaration introduces a fresh name, so contexts only grow.  A `Bool`, so its
proofs are `Eq.refl true` (the quoters rely on it). -/
def isFresh (C : Contract) (Γ : Ctx) (x : Name) : Bool :=
  (lookupBy x Γ).isNone && (C.rootType x).isNone

/-! ## Simple values, paths and values -/

/-- A simple value (KeY's `SimpleExpression`, the paper's `se`): a literal
or a stack local.  An update is built from simple parts, and a branch or a
guard tests one. -/
inductive Simple (C : Contract) (Γ : Ctx) : PrimTy → Type where
  /-- A number literal, `10`. -/
  | lit {p : PrimTy} (n : Int) (h : p.isNumeric = true) : Simple C Γ p
  /-- `true`, `false`. -/
  | bool (b : Bool) : Simple C Γ .bool
  /-- A stack local, `uint x = 1;` then `x`. -/
  | local {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p))) :
      Simple C Γ p

/-- How a reference type is indexed: a mapping by its key, an array by a
`uint`, each to its element type.  One `Loc.index` for both, so a rule that
does not care which (every Step 1 and Step 2 index rule) is one constructor;
the ones that do (`storageIndexWriteMappingSave`, `…ArraySave`) fix it. -/
inductive IndexTy : RefTy → PrimTy → Ty → Type where
  | map {k : PrimTy} {V : Ty} : IndexTy (.mapping (.prim k) V) k V
  | arr {E : Ty} : IndexTy (.array E) .uint E

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
  /-- A mapping entry `balances[i]`, or an array element `values[i]`. -/
  | index {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (b : SPath C Γ (.ref R))
      (i : Val C Γ k) : Loc C Γ V

/-- A value of primitive type `p`. -/
inductive Val (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | simple {p : PrimTy} (s : Simple C Γ p) : Val C Γ p
  /-- A storage read, `alice.age`. -/
  | read {p : PrimTy} (l : Loc C Γ (.prim p)) : Val C Γ p
  | binop {p : PrimTy} (op : BinOp) (h : op.accepts p = true) (a b : Val C Γ p) :
      Val C Γ (op.ret p)
  | unop {p : PrimTy} (op : UnOp) (h : op.accepts p = true) (a : Val C Γ p) :
      Val C Γ (op.ret p)

end

/-- The source of a storage write: a value at a primitive type, or a storage
path at a reference type, copied.  A copied type holds no mapping: solc ≥ 0.7
rejects the copy otherwise, and the interpreter is stuck on it
(`rhsToSVal`). -/
inductive Src (C : Contract) (Γ : Ctx) : Ty → Type where
  | val {p : PrimTy} (v : Val C Γ p) : Src C Γ (.prim p)
  | copy {R : RefTy} (p : SPath C Γ (.ref R)) (h : (Ty.ref R).mapFree = true) :
      Src C Γ (.ref R)

/-! ## Statements -/

mutual

/-- A statement, from context `Γ` to context `Γ'`. -/
inductive Stmt (C : Contract) : Ctx → Ctx → Type where
  /-- A storage write, `alice.age = 10;`, `alice = bob;`, `p.age = 1;`. -/
  | assign {Γ : Ctx} {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : Stmt C Γ Γ
  /-- `p = bob;` with `p` an alias: the alias now points at `bob`, nothing is
  copied. -/
  | rebind {Γ : Ctx} {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.path (.ref R)))
      (r : SPath C Γ (.ref R)) : Stmt C Γ Γ
  /-- `x = alice.age;` -/
  | assignLocal {Γ : Ctx} {p : PrimTy} (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim p))) (r : Val C Γ p) : Stmt C Γ Γ
  /-- `uint x;`, `uint x = e;`, with `x` fresh. -/
  | declLocal {Γ : Ctx} (p : PrimTy) (x : Name) (hx : isFresh C Γ x = true)
      (init : Option (Val C Γ p)) : Stmt C Γ (setBy x (.stack (.prim p)) Γ)
  /-- `Person storage p = alice;`, with `p` fresh.  `capture` marks the
  calculus's own alias capture, `T storage sp = nsp;`, which erases to a
  `storagePlaceAlias` rather than a `storageDecl`; the two run alike.  An
  uninitialised `T storage p;` is not a statement: solc ≥ 0.5 rejects it. -/
  | declStorage {Γ : Ctx} (capture : Bool) (R : RefTy) (x : Name)
      (hx : isFresh C Γ x = true) (init : SPath C Γ (.ref R)) :
      Stmt C Γ (setBy x (.path (.ref R)) Γ)
  /-- `delete alice.account;` -/
  | delete {Γ : Ctx} {T : Ty} (l : Loc C Γ T) : Stmt C Γ Γ
  /-- `if (c) { … } else { … }`, on a simple condition (the paper's
  `ifElseSplit`; `ksol` captures any other condition into a local first).  The
  branches declare nothing, as `stmtWt` requires. -/
  | ite {Γ : Ctx} (c : Simple C Γ .bool) (thn els : Prog C Γ Γ) : Stmt C Γ Γ
  /-- `require(c);`, on a simple condition (`requireSimple`). -/
  | require {Γ : Ctx} (c : Simple C Γ .bool) : Stmt C Γ Γ
  /-- `assert(c);`, on a simple condition (`assertSimple`). -/
  | assert {Γ : Ctx} (c : Simple C Γ .bool) : Stmt C Γ Γ
  | revert {Γ : Ctx} : Stmt C Γ Γ

/-- A block, threading the context through its statements. -/
inductive Prog (C : Contract) : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : Prog C Γ Γ
  | cons {Γ Γ₁ Γ₂ : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) : Prog C Γ Γ₂

end

/-- A block, then another. -/
def Prog.append {C : Contract} {Γ Γ₁ Γ₂ : Ctx} : Prog C Γ Γ₁ → Prog C Γ₁ Γ₂ → Prog C Γ Γ₂
  | .nil, Q => Q
  | .cons s P, Q => .cons s (P.append Q)

end Kernel
end Solidity
