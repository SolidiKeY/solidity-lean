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

/-! ## Fresh names -/

/-- The longest name a context or the contract binds. -/
def maxNameLen (C : Contract) (Γ : Ctx) : Nat :=
  ((Γ.map (·.1)) ++ C.vars.map (·.1)).foldl (fun n x => max n x.length) 0

/-- A fresh name: the first of `base`, `base1`, `base2`, … that is free, else
`base` padded past every name in scope, which no local and no state variable
can equal. -/
def freshName (C : Contract) (Γ : Ctx) (base : Name) : Name :=
  let cands := (List.range (Γ.length + C.vars.length + 1)).map fun k =>
    if k = 0 then base else base ++ toString k
  match cands.find? (isFresh C Γ ·) with
  | some x => x
  | none => base ++ String.mk (List.replicate (maxNameLen C Γ + 1) '#')

theorem foldl_max_ge (l : List Name) (n : Nat) : n ≤ l.foldl (fun n x => max n x.length) n := by
  induction l generalizing n with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem le_foldl_max {l : List Name} {x : Name} (hx : x ∈ l) (n : Nat) :
    x.length ≤ l.foldl (fun n x => max n x.length) n := by
  induction l generalizing n with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hm
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge _ _)
    · exact ih hm _

theorem lookupBy_none_of_long {α : Type} {l : List (Name × α)} {x : Name}
    (h : ∀ p ∈ l, p.1.length < x.length) : lookupBy x l = none := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    have hk : x ≠ k := fun he => by
      have := h (k, v) (List.mem_cons_self ..); subst he; exact Nat.lt_irrefl _ this
    simp only [lookupBy, if_neg hk]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- `freshName` is fresh.  At the context of `uint sp = 1;`, `sp` is taken,
so the capture a rule makes is called `sp1`. -/
theorem freshName_isFresh (C : Contract) (Γ : Ctx) (base : Name) :
    isFresh C Γ (freshName C Γ base) = true := by
  unfold freshName
  dsimp only
  split
  · next x hx => simpa using List.find?_some hx
  · simp only [isFresh, Bool.and_eq_true, Option.isNone_iff_eq_none]
    have hlen : maxNameLen C Γ < (base ++ String.mk (List.replicate (maxNameLen C Γ + 1) '#')).length := by
      rw [String.length_append]; simp; omega
    constructor
    · refine lookupBy_none_of_long fun p hp => Nat.lt_of_le_of_lt ?_ hlen
      exact le_foldl_max (List.mem_append_left _ (List.mem_map_of_mem hp)) 0
    · refine lookupBy_none_of_long fun p hp => Nat.lt_of_le_of_lt ?_ hlen
      exact le_foldl_max (List.mem_append_right _ (List.mem_map_of_mem hp)) 0

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

/-- A memory path of type `T` (KeY's `mv`/`nmp`): a memory local, or a
memory location. -/
inductive MPath (C : Contract) (Γ : Ctx) : Ty → Type where
  /-- A memory local, `Person memory m = alice;` then `m`. -/
  | var {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.mem (.ref R))) : MPath C Γ (.ref R)
  | loc {T : Ty} (l : MLoc C Γ T) : MPath C Γ T

/-- A memory location: a member or an element of a memory object (memory
has no mappings, and no roots of its own). -/
inductive MLoc (C : Contract) (Γ : Ctx) : Ty → Type where
  /-- `m.age` -/
  | field {s : Name} {T : Ty} (b : MPath C Γ (.struct s)) (f : Name)
      (h : C.fieldType s f = some T) : MLoc C Γ T
  /-- `xs[i]` -/
  | index {E : Ty} (b : MPath C Γ (.array E)) (i : Val C Γ .uint) : MLoc C Γ E

/-- A value of primitive type `p`. -/
inductive Val (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | simple {p : PrimTy} (s : Simple C Γ p) : Val C Γ p
  /-- A storage read, `alice.age`. -/
  | read {p : PrimTy} (l : Loc C Γ (.prim p)) : Val C Γ p
  /-- `a ⊕ b`, at the result type `q` of `⊕` at `p` (an equation, not a
  computed index, so a match at a fixed type can take it apart). -/
  | binop {p q : PrimTy} (op : BinOp) (h : op.accepts p = true) (hq : op.ret p = q)
      (a b : Val C Γ p) : Val C Γ q
  | unop {p q : PrimTy} (op : UnOp) (h : op.accepts p = true) (hq : op.ret p = q)
      (a : Val C Γ p) : Val C Γ q
  /-- `c ? a : b`, which evaluates only the branch it takes. -/
  | ternary {p : PrimTy} (c : Val C Γ .bool) (a b : Val C Γ p) : Val C Γ p
  /-- A memory read, `m.age`. -/
  | readMem {p : PrimTy} (l : MLoc C Γ (.prim p)) : Val C Γ p

end

/-- The source of a storage write: a value at a primitive type, or a storage
path at a reference type, copied.  A copied type holds no mapping: solc ≥ 0.7
rejects the copy otherwise, and the interpreter is stuck on it
(`rhsToSVal`). -/
inductive Src (C : Contract) (Γ : Ctx) : Ty → Type where
  | val {p : PrimTy} (v : Val C Γ p) : Src C Γ (.prim p)
  | copy {R : RefTy} (p : SPath C Γ (.ref R)) (h : (Ty.ref R).mapFree = true) :
      Src C Γ (.ref R)

/-- A simple path (`sp`): a state variable or an alias. -/
def SPath.isSimple {C : Contract} {Γ : Ctx} {T : Ty} : SPath C Γ T → Bool
  | .alias .. => true
  | .loc (.root ..) => true
  | .loc _ => false

/-- What a memory local is bound to: another memory object's identity
(aliasing, `m = n;`, `m = n.account;`). -/
inductive MRhs (C : Contract) (Γ : Ctx) (R : RefTy) where
  | alias (p : MPath C Γ (.ref R))

/-- What a memory location is written: a value, or a memory reference (by
identity: `m.account = n.account;` aliases). -/
inductive MSrc (C : Contract) (Γ : Ctx) : Ty → Type where
  | val {p : PrimTy} (v : Val C Γ p) : MSrc C Γ (.prim p)
  | ref {R : RefTy} (p : MPath C Γ (.ref R)) : MSrc C Γ (.ref R)

/-- The target of a compound assignment `l ⊕= e`: a stack local, a state
variable, a member, or an entry at a simple index (`ksol` captures any other
index first; the old table is stuck on one, and solkey has no taclet for
it). -/
inductive OpLoc (C : Contract) (Γ : Ctx) : PrimTy → Type where
  /-- `x += 1;` -/
  | local {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p))) : OpLoc C Γ p
  /-- `total += 1;` -/
  | root {p : PrimTy} (r : Name) (hΓ : lookupBy r Γ = none) (h : C.rootType r = some (.prim p)) :
      OpLoc C Γ p
  /-- `alice.age += 1;` -/
  | field {s : Name} {p : PrimTy} (b : SPath C Γ (.struct s)) (f : Name)
      (h : C.fieldType s f = some (.prim p)) : OpLoc C Γ p
  /-- `balances[i] += 1;` -/
  | index {R : RefTy} {k p : PrimTy} (it : IndexTy R k (.prim p)) (b : SPath C Γ (.ref R))
      (i : Simple C Γ k) : OpLoc C Γ p

/-- A target whose receiver, if it has one, is simple: `x`, `total`,
`sp.fld`, `sp[ie]`. -/
def OpLoc.recvSimple {C : Contract} {Γ : Ctx} {p : PrimTy} : OpLoc C Γ p → Bool
  | .field b _ _ | .index _ b _ => b.isSimple
  | _ => true

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
  /-- `alice.age += x;`, `x -= 1;`: `+= -= *= /= %=` (solkey's five), at a
  numeric type. -/
  | opAssign {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) : Stmt C Γ Γ
  /-- `x++;`, `++alice.age;`, `--x;`, at a numeric type. -/
  | incDec {Γ : Ctx} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
      Stmt C Γ Γ
  /-- `y = x++;`, `y = ++alice.age;`: into a stack local, from a target whose
  receiver is simple (no taclet takes another; `ksol` captures it first). -/
  | assignIncDec {Γ : Ctx} {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p)))
      (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) (hs : l.recvSimple = true) :
      Stmt C Γ Γ
  /-- `values.push(x);`, `persons.push(alice);`, `values.push();`: append a
  value, a copy, or (with no argument) the cleared slot, which needs the
  element type's default to be well-formed. -/
  | push {Γ : Ctx} {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
      (hd : (v.isSome || E.defaultOkS) = true) : Stmt C Γ Γ
  /-- `values.pop();` -/
  | pop {Γ : Ctx} {E : Ty} (b : SPath C Γ (.array E)) : Stmt C Γ Γ
  /-- `a.transfer(v);`: `v` of the contract's funds to `a`. -/
  | transfer {Γ : Ctx} (r a : Val C Γ .uint) : Stmt C Γ Γ
  /-- `Person memory m;` (a fresh default object) or `Person memory m = n;`. -/
  | declMem {Γ : Ctx} (R : RefTy) (x : Name) (hx : isFresh C Γ x = true)
      (init : Option (MRhs C Γ R)) (hd : (init.isSome || (Ty.ref R).defaultOkS) = true) :
      Stmt C Γ (setBy x (.mem (.ref R)) Γ)
  /-- `m = n;`: the memory local now names `n`'s object. -/
  | rebindMem {Γ : Ctx} {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.mem (.ref R)))
      (r : MRhs C Γ R) : Stmt C Γ Γ
  /-- `m.age = 3;`, `m.account = n.account;` -/
  | assignMem {Γ : Ctx} {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : Stmt C Γ Γ
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
