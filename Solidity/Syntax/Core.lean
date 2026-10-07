import Solidity.Syntax
import Solidity.Scope

/-!
# The typed syntax, scoped

`Syntax.lean`'s families with the locals in scope as an index
(`docs/intrinsic.md`, M2): every part is read in a context `Γ : Ctx`
(`Scope.lean`), a local is a position `Idx Γ t` that carries its type, and a
statement `Stmt C Γ Γ'` says which context it leaves.  So a local read
before it is declared, or at another type than declared, cannot be written,
and the locals check of `Syntax.lean` (`Stmt.wt`) holds by construction.

Scopes are explicit, as in solc: the branches of an `if` and of a `try`, a
loop's body and a block `{ … }` start from the enclosing context and their
locals end with them (the statement leaves `Γ`).  A call's body is closed
over a frame of its own, its return variables on its parameters
(`rs ++ ps`): the arguments are evaluated in the caller's context, and the
body sees nothing else.  What the call leaves in the caller's context is its
`CallRet`: nothing, a value assigned to a caller's local, or the return
variables themselves (a tuple's targets read them, and a memory return's
binding).

Names are labels on binders (`declLocal p x`, `Args.snoc`, `Binders`), not
part of the index (Gate G0, condition 3).  The printers keep them beside the
context, a `List Var` aligned with it, and write the same Solidity as
`Syntax.lean`'s.  `Stmt.wk` weakens a statement into a context with more
locals (`Thin`); it runs at elaboration time, so it may `match` on the
indexed families, which kernel-evaluated code may not (condition 1).

Until M4 these families live in `Solidity.Core` beside `Syntax.lean`'s,
which the elaborator still emits (Decision 8).
-/

namespace Solidity.Core

/-! ## Expressions -/

/-- A simple value (`se`): a literal of its type's range, a stack local, or
a value of the environment. -/
inductive Simple (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | lit {p : PrimTy} (n : Int) (h : p.inRange n = true) : Simple C Γ p
  | bool (b : Bool) : Simple C Γ .bool
  | local {p : PrimTy} (i : Idx Γ (.val p)) : Simple C Γ p
  | env {p : PrimTy} (k : EnvKey) (hp : p = .uint) : Simple C Γ p

mutual

/-- A storage path of type `T`: an alias (`lsv`), or a location. -/
inductive SPath (C : Contract) (Γ : Ctx) : Ty → Type where
  | alias {R : RefTy} (i : Idx Γ (.alias R)) : SPath C Γ (.ref R)
  | loc {T : Ty} (l : Loc C Γ T) : SPath C Γ T

/-- A storage location: a state variable, a member, an entry. -/
inductive Loc (C : Contract) (Γ : Ctx) : Ty → Type where
  | root {T : Ty} (r : Name) (h : C.rootType r = some T) : Loc C Γ T
  | field {s : Name} {T : Ty} (b : SPath C Γ (.struct s)) (f : Name)
      (h : C.fieldType s f = some T) : Loc C Γ T
  | index {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (b : SPath C Γ (.ref R))
      (i : Val C Γ k) : Loc C Γ V

/-- A memory path: a memory local (of a type that holds no mapping), or a
memory location. -/
inductive MPath (C : Contract) (Γ : Ctx) : Ty → Type where
  | var {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) : MPath C Γ (.ref R)
  | loc {T : Ty} (l : MLoc C Γ T) : MPath C Γ T

/-- A member or an element of a memory object. -/
inductive MLoc (C : Contract) (Γ : Ctx) : Ty → Type where
  | field {s : Name} {T : Ty} (b : MPath C Γ (.struct s)) (f : Name)
      (h : C.fieldType s f = some T) : MLoc C Γ T
  | index {R : RefTy} {E : Ty} (a : ArrTy R E) (b : MPath C Γ (.ref R)) (i : Val C Γ .uint) :
      MLoc C Γ E

/-- A value of primitive type `p`. -/
inductive Val (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | simple {p : PrimTy} (s : Simple C Γ p) : Val C Γ p
  | read {p : PrimTy} (l : Loc C Γ (.prim p)) : Val C Γ p
  | binop {p q : PrimTy} (op : BinOp) (h : op.accepts p = true) (hq : op.ret p = q)
      (a b : Val C Γ p) : Val C Γ q
  | unop {p q : PrimTy} (op : UnOp) (h : op.accepts p = true) (hq : op.ret p = q)
      (a : Val C Γ p) : Val C Γ q
  | ternary {p : PrimTy} (c : Val C Γ .bool) (a b : Val C Γ p) : Val C Γ p
  | readMem {p : PrimTy} (l : MLoc C Γ (.prim p)) : Val C Γ p
  | len {p : PrimTy} {E : Ty} (b : SPath C Γ (.array E)) (hp : p = .uint) : Val C Γ p
  | mlen {p : PrimTy} {E : Ty} (b : MPath C Γ (.array E)) (hp : p = .uint) : Val C Γ p

end

/-- The source of a storage write: a value, or a storage path copied. -/
inductive Src (C : Contract) (Γ : Ctx) : Ty → Type where
  | val {p : PrimTy} (v : Val C Γ p) : Src C Γ (.prim p)
  | copy {R : RefTy} (p : SPath C Γ (.ref R)) (h : (Ty.ref R).mapFree = true) : Src C Γ (.ref R)

/-- What a storage alias is bound to: a path, or the slot `b.push()` appends. -/
inductive ARhs (C : Contract) (Γ : Ctx) (R : RefTy) where
  | path (p : SPath C Γ (.ref R))
  | push (b : SPath C Γ (.array (.ref R))) (hd : (Ty.ref R).defaultOkS = true)

/-- What a memory local is bound to: an object by identity, a deep copy of a
storage object, or a fresh array. -/
inductive MRhs (C : Contract) (Γ : Ctx) (R : RefTy) where
  | alias (p : MPath C Γ (.ref R))
  | copy (p : SPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true)
  | newArr (n : Simple C Γ .uint) (h : R.newArrOk = true)

mutual
theorem MPath.mapFree {C : Contract} {Γ : Ctx} : {T : Ty} → MPath C Γ T → T.mapFree = true
  | _, .var _ hm => hm
  | _, .loc l => l.mapFree
theorem MLoc.mapFree {C : Contract} {Γ : Ctx} : {T : Ty} → MLoc C Γ T → T.mapFree = true
  | _, .field b _ h => Ty.mapFree_field b.mapFree h
  | _, .index .dyn b _ => b.mapFree
  | _, .index .fixed b _ => b.mapFree
end

theorem MRhs.mapFree {C : Contract} {Γ : Ctx} {R : RefTy} :
    MRhs C Γ R → (Ty.ref R).mapFree = true
  | .alias p => p.mapFree
  | .copy _ hm => hm
  | .newArr _ h => by
    cases R <;> simp only [RefTy.newArrOk, Bool.and_eq_true, Bool.false_eq_true] at h
    exact h.1

/-- Where a fresh array lands when it is not bound to a memory local. -/
inductive NewLhs (C : Contract) (Γ : Ctx) : RefTy → Type where
  | store {R : RefTy} (l : Loc C Γ (.ref R)) : NewLhs C Γ R
  | mem {R : RefTy} (l : MLoc C Γ (.ref R)) : NewLhs C Γ R

/-- What a memory location is written: a value, or a memory reference. -/
inductive MSrc (C : Contract) (Γ : Ctx) : Ty → Type where
  | val {p : PrimTy} (v : Val C Γ p) : MSrc C Γ (.prim p)
  | ref {R : RefTy} (p : MPath C Γ (.ref R)) : MSrc C Γ (.ref R)

/-- The target of `l ⊕= e` and `l++`. -/
inductive OpLoc (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | local {p : PrimTy} (i : Idx Γ (.val p)) : OpLoc C Γ p
  | root {p : PrimTy} (r : Name) (h : C.rootType r = some (.prim p)) : OpLoc C Γ p
  | field {s : Name} {p : PrimTy} (b : SPath C Γ (.struct s)) (f : Name)
      (h : C.fieldType s f = some (.prim p)) : OpLoc C Γ p
  | index {R : RefTy} {k p : PrimTy} (it : IndexTy R k (.prim p)) (b : SPath C Γ (.ref R))
      (i : Simple C Γ k) : OpLoc C Γ p
  | mfield {s : Name} {p : PrimTy} (b : MPath C Γ (.struct s)) (f : Name)
      (h : C.fieldType s f = some (.prim p)) : OpLoc C Γ p
  | mindex {R : RefTy} {p : PrimTy} (a : ArrTy R (.prim p)) (b : MPath C Γ (.ref R))
      (i : Simple C Γ .uint) : OpLoc C Γ p

/-! ### Which parts are simple -/

def Val.isSimple {C : Contract} {Γ : Ctx} {p : PrimTy} : Val C Γ p → Bool
  | .simple _ => true
  | _ => false

def SPath.isSimple {C : Contract} {Γ : Ctx} {T : Ty} : SPath C Γ T → Bool
  | .alias _ => true
  | .loc (.root ..) => true
  | .loc _ => false

def MPath.isSimple {C : Contract} {Γ : Ctx} {T : Ty} : MPath C Γ T → Bool
  | .var .. => true
  | .loc _ => false

def OpLoc.recvSimple {C : Contract} {Γ : Ctx} {p : PrimTy} : OpLoc C Γ p → Bool
  | .field b _ _ | .index _ b _ => b.isSimple
  | .mfield b _ _ | .mindex _ b _ => b.isSimple
  | _ => true

def Val.toSimple? {C : Contract} {Γ : Ctx} {p : PrimTy} : Val C Γ p → Option (Simple C Γ p)
  | .simple s => some s
  | _ => none

/-! ## Calls -/

/-- A call's arguments, each the value `e` its parameter `x : p` is bound
to, in the order they are bound: the last is innermost in the frame `ps`.
Every argument is evaluated in the caller's context `Γ`. -/
inductive Args (C : Contract) (Γ : Ctx) : Ctx → Type where
  | nil : Args C Γ []
  | snoc {ps : Ctx} (as : Args C Γ ps) (p : PrimTy) (x : Var) (e : Val C Γ p) :
      Args C Γ (.val p :: ps)

/-- What a call does with its return variables `rs`, which its frame
declares at their defaults on its parameters, and the context `Γ'` it
leaves the caller in:

* `none`: no return variable (a function of several returns called as a
  statement declares them in its body);
* `val p r res`: one, `r`, its value assigned to the caller's `res` if the
  call is assigned (`y = f(a);`);
* `rets bs`: several (or one with a target), left in the caller's context,
  where the tuple's targets read them (`(lo, hi) = f(a);` is the call and
  `lo = r0; hi = r1;`), KeY's `functionBodyExpand`;
* `mem R r`: a memory return, a fresh default object (as solc allocates one
  on entry), left in the caller's context for the statement after the call
  to bind (`Person memory m = f();` is the call and `Person memory m = r;`). -/
inductive CallRet (Γ : Ctx) : Ctx → Ctx → Type where
  | none : CallRet Γ [] Γ
  | val (p : PrimTy) (r : Var) (res : Option (Idx Γ (.val p))) : CallRet Γ [.val p] Γ
  | rets {rs : Ctx} (bs : Binders rs) : CallRet Γ rs (rs ++ Γ)
  | mem (R : RefTy) (r : Var) (hd : (Ty.ref R).defaultOkS = true)
      (hm : (Ty.ref R).mapFree = true) : CallRet Γ [.mem R] (.mem R :: Γ)

/-- An argument of an external call, at its type. -/
abbrev ExtArg (C : Contract) (Γ : Ctx) := (p : PrimTy) × Simple C Γ p

/-- `a.f(e₁, …, eₙ)`: an external call, its receiver and arguments simple. -/
structure ExtCall (C : Contract) (Γ : Ctx) where
  addr : Simple C Γ .uint
  fn : Name
  args : List (ExtArg C Γ)

/-- What a loop is proved by: unwound at most `k` times, or by its invariant
and variant (read in the loop's context). -/
inductive LoopAnn (C : Contract) (Γ : Ctx) where
  | unwind (k : Nat)
  | inv (I : Val C Γ .bool) (dec : Option (Val C Γ .uint))

/-! ## Statements -/

mutual

/-- A statement of contract `C`, read in `Γ`, leaving `Γ'`: a declaration
pushes its local, a call may leave its return variables, every other
statement leaves `Γ`. -/
inductive Stmt (C : Contract) : Ctx → Ctx → Type where
  | assign {Γ : Ctx} {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : Stmt C Γ Γ
  | rebind {Γ : Ctx} {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) : Stmt C Γ Γ
  | assignLocal {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) : Stmt C Γ Γ
  | declLocal {Γ : Ctx} (p : PrimTy) (x : Var) (init : Option (Val C Γ p)) :
      Stmt C Γ (.val p :: Γ)
  /-- `Person storage lsv = sp;`, and `Person storage lsv;`, an unset alias
  through which a read reverts. -/
  | declStorage {Γ : Ctx} (R : RefTy) (x : Var) (init : Option (ARhs C Γ R)) :
      Stmt C Γ (.alias R :: Γ)
  | opAssign {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) : Stmt C Γ Γ
  | incDec {Γ : Ctx} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
      Stmt C Γ Γ
  | assignIncDec {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
      (hp : p.isNumeric = true) (l : OpLoc C Γ p) (hs : l.recvSimple = true) : Stmt C Γ Γ
  | push {Γ : Ctx} {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
      (hd : (v.isSome || E.defaultOkS) = true) : Stmt C Γ Γ
  | pop {Γ : Ctx} {E : Ty} (b : SPath C Γ (.array E)) : Stmt C Γ Γ
  | transfer {Γ : Ctx} (r a : Val C Γ .uint) : Stmt C Γ Γ
  | send {Γ : Ctx} (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) : Stmt C Γ Γ
  | declMem {Γ : Ctx} (R : RefTy) (x : Var) (init : Option (MRhs C Γ R))
      (hd : (init.isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
      Stmt C Γ (.mem R :: Γ)
  | rebindMem {Γ : Ctx} {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) : Stmt C Γ Γ
  | assignFromMem {Γ : Ctx} {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
      Stmt C Γ Γ
  | assignMem {Γ : Ctx} {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : Stmt C Γ Γ
  | delete {Γ : Ctx} {T : Ty} (l : Loc C Γ T) : Stmt C Γ Γ
  | deleteMem {Γ : Ctx} {T : Ty} (p : MPath C Γ T) (hd : T.defaultOkS = true) : Stmt C Γ Γ
  | assignNew {Γ : Ctx} {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
      (h : R.newArrOk = true) : Stmt C Γ Γ
  /-- `if (c) { … } else { … }`: each branch a scope. -/
  | ite {Γ Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) : Stmt C Γ Γ
  | require {Γ : Ctx} (c : Val C Γ .bool) : Stmt C Γ Γ
  | assert {Γ : Ctx} (c : Val C Γ .bool) : Stmt C Γ Γ
  | revert {Γ : Ctx} : Stmt C Γ Γ
  /-- An internal call of `f`: the arguments bound to the parameters `ps`,
  the return variables `rs` declared on them, the body run in that frame. -/
  | call {Γ Γ' ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
      (body : Prog C (rs ++ ps) Γf) : Stmt C Γ Γ'
  /-- `try a.f(e) returns (…) { ok } catch Error(string memory) { err }
  catch Panic(uint c) { panic } catch { other }`: `ok` sees the returned
  values `rets`, `panic` the code. -/
  | tryCall {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
      (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (code : CodeBinder κ)
      (panic : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) : Stmt C Γ Γ
  /-- `while (c) { … }`: the body a scope, popped every iteration. -/
  | loop {Γ Γ₁ : Ctx} (a : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Γ₁) : Stmt C Γ Γ
  /-- `{ … }`: a block, its locals ending with it. -/
  | block {Γ Γ₁ : Ctx} (body : Prog C Γ Γ₁) : Stmt C Γ Γ

/-- A sequence of statements, each read where the one before leaves. -/
inductive Prog (C : Contract) : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : Prog C Γ Γ
  | cons {Γ Γ₁ Γ₂ : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) : Prog C Γ Γ₂

end

/-! ## Printing

The printers write `Syntax.lean`'s Solidity: `ns` are the names of the
locals of the context, innermost first. -/

section Print

variable {C : Contract} [FreshNames]

def Simple.toStr {Γ : Ctx} {p : PrimTy} (ns : List Var) : Simple C Γ p → String
  | .lit n _ => toString n
  | .bool b => toString b
  | .local i => toString (i.name ns)
  | .env k _ => k.toStr

mutual

def SPath.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : SPath C Γ T → String
  | .alias i => toString (i.name ns)
  | .loc l => l.toStr ns

def Loc.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : Loc C Γ T → String
  | .root r _ => r
  | .field b f _ => s!"{b.toStr ns}.{f}"
  | .index _ b i => s!"{b.toStr ns}[{i.toStr ns true}]"

def MPath.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : MPath C Γ T → String
  | .var i _ => toString (i.name ns)
  | .loc l => l.toStr ns

def MLoc.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : MLoc C Γ T → String
  | .field b f _ => s!"{b.toStr ns}.{f}"
  | .index _ b i => s!"{b.toStr ns}[{i.toStr ns true}]"

/-- `top` is whether the value stands alone, so needs no parentheses. -/
def Val.toStr {Γ : Ctx} {p : PrimTy} (ns : List Var) : Val C Γ p → (top : Bool := false) → String
  | .simple s, _ => s.toStr ns
  | .read l, _ => l.toStr ns
  | .binop op _ _ a b, top =>
    let s := s!"{a.toStr ns} {BinOp.sym op} {b.toStr ns}"
    if top then s else s!"({s})"
  | .unop op _ _ a, _ => s!"{UnOp.sym op}{a.toStr ns}"
  | .ternary c a b, top =>
    let s := s!"{c.toStr ns} ? {a.toStr ns} : {b.toStr ns}"
    if top then s else s!"({s})"
  | .readMem l, _ => l.toStr ns
  | .len b _, _ => s!"{b.toStr ns}.length"
  | .mlen b _, _ => s!"{b.toStr ns}.length"

end

def Src.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : Src C Γ T → String
  | .val v => v.toStr ns true
  | .copy p _ => p.toStr ns

def ARhs.toStr {Γ : Ctx} {R : RefTy} (ns : List Var) : ARhs C Γ R → String
  | .path p => p.toStr ns
  | .push b _ => s!"{b.toStr ns}.push()"

def OpLoc.toStr {Γ : Ctx} {p : PrimTy} (ns : List Var) : OpLoc C Γ p → String
  | .local i => toString (i.name ns)
  | .root r _ => r
  | .field b f _ => s!"{b.toStr ns}.{f}"
  | .index _ b i => s!"{b.toStr ns}[{i.toStr ns}]"
  | .mfield b f _ => s!"{b.toStr ns}.{f}"
  | .mindex _ b i => s!"{b.toStr ns}[{i.toStr ns}]"

def MRhs.toStr {Γ : Ctx} {R : RefTy} (ns : List Var) : MRhs C Γ R → String
  | .alias p => p.toStr ns
  | .copy p _ => p.toStr ns
  | .newArr n _ => s!"new {Ty.toStr (.ref R)}({n.toStr ns})"

def NewLhs.toStr {Γ : Ctx} {R : RefTy} (ns : List Var) : NewLhs C Γ R → String
  | .store l => l.toStr ns
  | .mem l => l.toStr ns

def MSrc.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : MSrc C Γ T → String
  | .val v => v.toStr ns true
  | .ref p => p.toStr ns

def LoopAnn.toStr {Γ : Ctx} (ns : List Var) : LoopAnn C Γ → String
  | .unwind 0 => ""
  | .unwind k => s!"/// @custom:key unwind {k} "
  | .inv I dec =>
    s!"/// @custom:key invariant {I.toStr ns true} " ++
      ((dec.map fun d => s!"/// @custom:key decreases {d.toStr ns true} ").getD "")

/-- The arguments as written, in order. -/
def Args.toStrs {Γ : Ctx} (ns : List Var) : {ps : Ctx} → Args C Γ ps → List String
  | _, .nil => []
  | _, .snoc as _ _ e => as.toStrs ns ++ [e.toStr ns true]

/-- The parameters' names, innermost first: the frame's names below the
return variables. -/
def Args.names {Γ : Ctx} : {ps : Ctx} → Args C Γ ps → List Var
  | _, .nil => []
  | _, .snoc as _ x _ => x :: as.names

/-- The return variables' names, innermost first. -/
def CallRet.names {Γ : Ctx} : {rs Γ' : Ctx} → CallRet Γ rs Γ' → List Var
  | _, _, .none => []
  | _, _, .val _ r _ => [r]
  | _, _, .rets bs => bs.names
  | _, _, .mem _ r _ _ => [r]

/-- The names of the context a call leaves its caller in. -/
def CallRet.outNames {Γ : Ctx} (ns : List Var) : {rs Γ' : Ctx} → CallRet Γ rs Γ' → List Var
  | _, _, .none => ns
  | _, _, .val .. => ns
  | _, _, .rets bs => bs.names ++ ns
  | _, _, .mem _ r _ _ => r :: ns

/-- The names of the context a statement leaves. -/
def Stmt.outNames {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → List Var
  | .declLocal _ x _ => x :: ns
  | .declStorage _ x _ => x :: ns
  | .declMem _ x .. => x :: ns
  | .call _ _ ret _ => ret.outNames ns
  | _ => ns

/-- `f(e₁, …, eₙ);` -/
def callStr {Γ : Ctx} {ps : Ctx} (ns : List Var) (f : Name) (args : Args C Γ ps) : String :=
  s!"{f}({", ".intercalate (args.toStrs ns)});"

/-- A call returning a memory reference: its return variable and the call. -/
def Stmt.memRet? {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → Option (Var × String)
  | .call f args (.mem _ r _ _) _ => some (r, callStr ns f args)
  | _ => none

/-- A statement binding a memory local to a local (`Person memory m = r;`,
`m = r;`): the local read, and how the statement writes with the call in
its place. -/
def Stmt.bindsMem? {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → Option (Var × (String → String))
  | .declMem R x (some (.alias (.var i _))) _ _ =>
    some (i.name ns, fun c => s!"{Ty.toStr (.ref R)} memory {x} = {c}")
  | .rebindMem x (.alias (.var i _)) =>
    some (i.name ns, fun c => s!"{x.name ns} = {c}")
  | _ => none

/-- A memory call and the statement after it that binds its return
variable, written as the statement they are elaborated from. -/
def Stmt.memCallStr? {Γ Γ₁ Γ₂ : Ctx} (ns : List Var) (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) :
    Option String :=
  match s.memRet? ns, P with
  | some (r, c), .cons t _ =>
    match t.bindsMem? (s.outNames ns) with
    | some (r', w) => if r' = r then some (w c) else none
    | none => none
  | _, _ => none

/-- The target a statement after a call of several returns assigns one of
them to (`lo = r0;`): the return's position among `rs`, and the target. -/
def Stmt.retTarget? {Γ Γ' : Ctx} (rs : List Var) (ns : List Var) :
    Stmt C Γ Γ' → Option (Nat × String)
  | .assignLocal x (.simple (.local r)) => (rs.findIdx? (· == r.name ns)).map (·, toString (x.name ns))
  | .assign l (.val (.simple (.local r))) => (rs.findIdx? (· == r.name ns)).map (·, l.toStr ns)
  | .assignMem l (.val (.simple (.local r))) => (rs.findIdx? (· == r.name ns)).map (·, l.toStr ns)
  | _ => none

/-- The statements after a call of several returns that assign them, in
their order, from the `start`-th return on. -/
def Prog.retTargets {Γ Γ' : Ctx} (rs : List Var) (start : Nat) (ns : List Var) :
    Prog C Γ Γ' → List (Nat × String)
  | .nil => []
  | .cons s P =>
    match s.retTarget? rs ns with
    | some (i, t) => if start ≤ i then (i, t) :: Prog.retTargets rs (i + 1) (s.outNames ns) P else []
    | none => []

/-- A call of several returns: their names in order, and the call. -/
def Stmt.tupleRets? {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → Option (List Var × String)
  | .call f args (.rets bs) _ => some (bs.toList.map (·.2), callStr ns f args)
  | _ => none

/-- A call of several returns and the statements after it that assign them,
written as the tuple assignment they are elaborated from, with the number
of statements after the call it covers. -/
def Stmt.tupleCallStr? {Γ Γ₁ Γ₂ : Ctx} (ns : List Var) (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) :
    Option (String × Nat) :=
  match s.tupleRets? ns with
  | none => none
  | some (rs, cs) =>
    let ts := Prog.retTargets rs 0 (s.outNames ns) P
    if ts.isEmpty then
      if rs.length < 2 then none
      else some (s!"({String.mk (List.replicate (rs.length - 1) ',')}) = {cs}", 0)
    else if rs.length == 1 then some (s!"{((ts.head?).map (·.2)).getD ""} = {cs}", ts.length)
    else
      let slots := (List.range rs.length).map fun i => ((ts.find? (·.1 == i)).map (·.2)).getD ""
      some (s!"({", ".intercalate slots}) = {cs}", ts.length)

mutual

def Stmt.toStr {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → String
  | .assign l r => s!"{l.toStr ns} = {r.toStr ns};"
  | .rebind x r => s!"{x.name ns} = {r.toStr ns};"
  | .assignLocal x r => s!"{x.name ns} = {r.toStr ns true};"
  | .declLocal p x init =>
    match init with
    | none => s!"{Ty.toStr (.prim p)} {x};"
    | some e => s!"{Ty.toStr (.prim p)} {x} = {e.toStr ns true};"
  | .declStorage R x init =>
    match init with
    | none => s!"{Ty.toStr (.ref R)} storage {x};"
    | some e => s!"{Ty.toStr (.ref R)} storage {x} = {e.toStr ns};"
  | .declMem R x init _ _ =>
    match init with
    | none => s!"{Ty.toStr (.ref R)} memory {x};"
    | some r => s!"{Ty.toStr (.ref R)} memory {x} = {r.toStr ns};"
  | .rebindMem x r => s!"{x.name ns} = {r.toStr ns};"
  | .assignMem l r => s!"{l.toStr ns} = {r.toStr ns};"
  | .assignFromMem l p => s!"{l.toStr ns} = {p.toStr ns};"
  | .opAssign op _ _ l r => s!"{l.toStr ns} {BinOp.sym op}= {r.toStr ns true};"
  | .incDec op _ l => s!"{IncDec.show op (l.toStr ns)};"
  | .push b v _ =>
    match v with
    | none => s!"{b.toStr ns}.push();"
    | some r => s!"{b.toStr ns}.push({r.toStr ns});"
  | .pop b => s!"{b.toStr ns}.pop();"
  | .transfer r a => s!"{r.toStr ns}.transfer({a.toStr ns true});"
  | .send pv r a => s!"{pv.name ns} = {r.toStr ns}.send({a.toStr ns true});"
  | .assignIncDec x op _ l _ => s!"{x.name ns} = {IncDec.show op (l.toStr ns)};"
  | .delete l => s!"delete {l.toStr ns};"
  | .deleteMem p _ => s!"delete {p.toStr ns};"
  | .assignNew (R := R) l n _ => s!"{l.toStr ns} = new {Ty.toStr (.ref R)}({n.toStr ns});"
  | .ite c thn els =>
    s!"if ({c.toStr ns true}) {braced (Prog.toStrs 0 ns thn)} else {braced (Prog.toStrs 0 ns els)}"
  | .require c => s!"require({c.toStr ns true});"
  | .assert c => s!"assert({c.toStr ns true});"
  | .revert => "revert();"
  | .call f args ret _ =>
    let call := callStr ns f args
    match ret with
    | .val _ _ (some y) => s!"{y.name ns} = {call}"
    | _ => call
  | .tryCall c rets ok err code pnc other =>
    let args := ", ".intercalate (c.args.map fun a => a.2.toStr ns)
    let rs := rets.toList
    let retsS := if rs.isEmpty then "" else
      s!" returns ({", ".intercalate (rs.map fun (p, x) => s!"{Ty.toStr (.prim p)} {x}")})"
    let codeS := match code.names with
      | [x] => s!"uint {x}"
      | _ => "uint"
    s!"try address({c.addr.toStr ns}).{c.fn}({args}){retsS} \
      {braced (Prog.toStrs 0 (rets.names ++ ns) ok)} \
      catch Error(string memory) {braced (Prog.toStrs 0 ns err)} \
      catch Panic({codeS}) {braced (Prog.toStrs 0 (code.names ++ ns) pnc)} \
      catch {braced (Prog.toStrs 0 ns other)}"
  | .loop a c body =>
    s!"{a.toStr ns}while ({c.toStr ns true}) {braced (Prog.toStrs 0 ns body)}"
  | .block body => braced (Prog.toStrs 0 ns body)

/-- The statements of a block, one string each; a memory call and the
statement binding its result are one, and so are a call of several returns
and the statements assigning them, the statements after the first skipped
(`skip` of them). -/
def Prog.toStrs {Γ Γ' : Ctx} (skip : Nat) (ns : List Var) : Prog C Γ Γ' → List String
  | .nil => []
  | .cons s P =>
    match skip with
    | k + 1 => Prog.toStrs k (s.outNames ns) P
    | 0 =>
      match Stmt.tupleCallStr? ns s P with
      | some (c, k) => c :: Prog.toStrs k (s.outNames ns) P
      | none =>
        match Stmt.memCallStr? ns s P with
        | some c => c :: Prog.toStrs 1 (s.outNames ns) P
        | none => s.toStr ns :: Prog.toStrs 0 (s.outNames ns) P

end

/-- A block, as the Solidity it came from. -/
def Prog.toStr {Γ Γ' : Ctx} (ns : List Var) (P : Prog C Γ Γ') : String :=
  " ".intercalate (Prog.toStrs 0 ns P)

/-- One statement per line, for display. -/
def Prog.show {Γ Γ' : Ctx} (ns : List Var) (P : Prog C Γ Γ') : String :=
  "\n".intercalate (Prog.toStrs 0 ns P)

end Print

/-! ## Weakening

A part read in `Γ` is read in any `Δ` that `Γ` thins into: every position
moves (`Idx.wk`).  A statement also returns the context it leaves in `Δ`,
with the thinning of its own output into it, to weaken what follows. -/

section Weaken

variable {C : Contract}

def Simple.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} : Simple C Γ p → Simple C Δ p
  | .lit n hr => .lit n hr
  | .bool b => .bool b
  | .local i => .local (i.wk h)
  | .env k hp => .env k hp

mutual

def SPath.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : SPath C Γ T → SPath C Δ T
  | .alias i => .alias (i.wk h)
  | .loc l => .loc (l.wk h)

def Loc.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : Loc C Γ T → Loc C Δ T
  | .root r hr => .root r hr
  | .field b f hf => .field (b.wk h) f hf
  | .index it b i => .index it (b.wk h) (i.wk h)

def MPath.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : MPath C Γ T → MPath C Δ T
  | .var i hm => .var (i.wk h) hm
  | .loc l => .loc (l.wk h)

def MLoc.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : MLoc C Γ T → MLoc C Δ T
  | .field b f hf => .field (b.wk h) f hf
  | .index a b i => .index a (b.wk h) (i.wk h)

def Val.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} : Val C Γ p → Val C Δ p
  | .simple s => .simple (s.wk h)
  | .read l => .read (l.wk h)
  | .binop op ha hq a b => .binop op ha hq (a.wk h) (b.wk h)
  | .unop op ha hq a => .unop op ha hq (a.wk h)
  | .ternary c a b => .ternary (c.wk h) (a.wk h) (b.wk h)
  | .readMem l => .readMem (l.wk h)
  | .len b hp => .len (b.wk h) hp
  | .mlen b hp => .mlen (b.wk h) hp

end

def Src.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : Src C Γ T → Src C Δ T
  | .val v => .val (v.wk h)
  | .copy p hm => .copy (p.wk h) hm

def ARhs.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {R : RefTy} : ARhs C Γ R → ARhs C Δ R
  | .path p => .path (p.wk h)
  | .push b hd => .push (b.wk h) hd

def MRhs.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {R : RefTy} : MRhs C Γ R → MRhs C Δ R
  | .alias p => .alias (p.wk h)
  | .copy p hm => .copy (p.wk h) hm
  | .newArr n hn => .newArr (n.wk h) hn

def NewLhs.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {R : RefTy} : NewLhs C Γ R → NewLhs C Δ R
  | .store l => .store (l.wk h)
  | .mem l => .mem (l.wk h)

def MSrc.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : MSrc C Γ T → MSrc C Δ T
  | .val v => .val (v.wk h)
  | .ref p => .ref (p.wk h)

def OpLoc.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} : OpLoc C Γ p → OpLoc C Δ p
  | .local i => .local (i.wk h)
  | .root r hr => .root r hr
  | .field b f hf => .field (b.wk h) f hf
  | .index it b i => .index it (b.wk h) (i.wk h)
  | .mfield b f hf => .mfield (b.wk h) f hf
  | .mindex a b i => .mindex a (b.wk h) (i.wk h)

theorem SPath.isSimple_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} (b : SPath C Γ T) :
    (b.wk h).isSimple = b.isSimple := by
  rcases b with _ | (_ | _ | _) <;> rfl

theorem MPath.isSimple_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} (b : MPath C Γ T) :
    (b.wk h).isSimple = b.isSimple := by
  cases b <;> rfl

theorem OpLoc.recvSimple_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} (l : OpLoc C Γ p) :
    (l.wk h).recvSimple = l.recvSimple := by
  cases l <;> first | rfl | exact SPath.isSimple_wk h _ | exact MPath.isSimple_wk h _

def ExtCall.wk {Γ Δ : Ctx} (h : Thin Γ Δ) (c : ExtCall C Γ) : ExtCall C Δ :=
  ⟨c.addr.wk h, c.fn, c.args.map fun a => ⟨a.1, a.2.wk h⟩⟩

def LoopAnn.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : LoopAnn C Γ → LoopAnn C Δ
  | .unwind k => .unwind k
  | .inv I dec => .inv (I.wk h) (dec.map (·.wk h))

def Args.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {ps : Ctx} → Args C Γ ps → Args C Δ ps
  | _, .nil => .nil
  | _, .snoc as p x e => .snoc (as.wk h) p x (e.wk h)

/-- A call's result weakened: the context it leaves in `Δ`, and how its own
output thins into it. -/
def CallRet.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {rs Γ' : Ctx} → CallRet Γ rs Γ' →
    (Δ' : Ctx) × Thin Γ' Δ' × CallRet Δ rs Δ'
  | _, _, .none => ⟨Δ, h, .none⟩
  | _, _, .val p r res => ⟨Δ, h, .val p r (res.map (·.wk h))⟩
  | rs, _, .rets bs => ⟨rs ++ Δ, Thin.keepAll rs h, .rets bs⟩
  | _, _, .mem R r hd hm => ⟨.mem R :: Δ, .keep h, .mem R r hd hm⟩

mutual

/-- Weakening a statement: the output context is computed, with the
thinning that relates it to the old one.  A call's body is closed over its
frame, so it is not touched. -/
def Stmt.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {Γ' : Ctx} → Stmt C Γ Γ' →
    (Δ' : Ctx) × Thin Γ' Δ' × Stmt C Δ Δ'
  | _, .assign l r => ⟨Δ, h, .assign (l.wk h) (r.wk h)⟩
  | _, .rebind i r => ⟨Δ, h, .rebind (i.wk h) (r.wk h)⟩
  | _, .assignLocal i r => ⟨Δ, h, .assignLocal (i.wk h) (r.wk h)⟩
  | _, .declLocal p x init => ⟨_, .keep h, .declLocal p x (init.map (·.wk h))⟩
  | _, .declStorage R x init => ⟨_, .keep h, .declStorage R x (init.map (·.wk h))⟩
  | _, .opAssign op hop hp l r => ⟨Δ, h, .opAssign op hop hp (l.wk h) (r.wk h)⟩
  | _, .incDec op hp l => ⟨Δ, h, .incDec op hp (l.wk h)⟩
  | _, .assignIncDec i op hp l hs =>
    ⟨Δ, h, .assignIncDec (i.wk h) op hp (l.wk h) ((OpLoc.recvSimple_wk h l).trans hs)⟩
  | _, .push b v hd =>
    ⟨Δ, h, .push (b.wk h) (v.map (·.wk h)) (by rw [Option.isSome_map]; exact hd)⟩
  | _, .pop b => ⟨Δ, h, .pop (b.wk h)⟩
  | _, .transfer r a => ⟨Δ, h, .transfer (r.wk h) (a.wk h)⟩
  | _, .send pv r a => ⟨Δ, h, .send (pv.wk h) (r.wk h) (a.wk h)⟩
  | _, .declMem R x init hd hm =>
    ⟨_, .keep h, .declMem R x (init.map (·.wk h)) (by rw [Option.isSome_map]; exact hd) hm⟩
  | _, .rebindMem i r => ⟨Δ, h, .rebindMem (i.wk h) (r.wk h)⟩
  | _, .assignFromMem l p => ⟨Δ, h, .assignFromMem (l.wk h) (p.wk h)⟩
  | _, .assignMem l r => ⟨Δ, h, .assignMem (l.wk h) (r.wk h)⟩
  | _, .delete l => ⟨Δ, h, .delete (l.wk h)⟩
  | _, .deleteMem p hd => ⟨Δ, h, .deleteMem (p.wk h) hd⟩
  | _, .assignNew l n hn => ⟨Δ, h, .assignNew (l.wk h) (n.wk h) hn⟩
  | _, .ite c thn els => ⟨Δ, h, .ite (c.wk h) (thn.wk h).2.2 (els.wk h).2.2⟩
  | _, .require c => ⟨Δ, h, .require (c.wk h)⟩
  | _, .assert c => ⟨Δ, h, .assert (c.wk h)⟩
  | _, .revert => ⟨Δ, h, .revert⟩
  | _, .call f args ret body =>
    let ⟨Δ', h', ret'⟩ := ret.wk h
    ⟨Δ', h', .call f (args.wk h) ret' body⟩
  | _, @Stmt.tryCall _ _ ρ κ _ _ _ _ c rets ok err code pnc other =>
    ⟨Δ, h, .tryCall (c.wk h) rets (ok.wk (Thin.keepAll ρ h)).2.2 (err.wk h).2.2 code
      (pnc.wk (Thin.keepAll κ h)).2.2 (other.wk h).2.2⟩
  | _, .loop a c body => ⟨Δ, h, .loop (a.wk h) (c.wk h) (body.wk h).2.2⟩
  | _, .block body => ⟨Δ, h, .block (body.wk h).2.2⟩

def Prog.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {Γ' : Ctx} → Prog C Γ Γ' →
    (Δ' : Ctx) × Thin Γ' Δ' × Prog C Δ Δ'
  | _, .nil => ⟨Δ, h, .nil⟩
  | _, .cons s P =>
    let ⟨_, h₁, s'⟩ := s.wk h
    let ⟨Δ₂, h₂, P'⟩ := P.wk h₁
    ⟨Δ₂, h₂, .cons s' P'⟩

end

end Weaken

/-! ## An example

Every scope at once over `StandardExample`, printed as `Syntax.lean` prints
the same statements (`tour`, `Stmt.memCallStr?`, `Stmt.tupleCallStr?`). -/

section Example

private abbrev SE := StandardExample
private abbrev P : RefTy := .struct "Person"

private def alice {Γ : Ctx} : SPath SE Γ (.struct "Person") := .loc (.root "alice" rfl)
private def lit {Γ : Ctx} (n : Int) (h : PrimTy.uint.inRange n = true := by rfl) : Val SE Γ .uint :=
  .simple (.lit n h)
private def loc {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p)) : Val SE Γ p := .simple (.local i)

/-- `x`, `p`, `r` (a memory return), `m`, and the tuple's `r0`, `r1`. -/
private def example₁ : Prog SE [] [.val .uint, .val .uint, .mem P, .mem P, .alias P, .val .uint] :=
  .cons (.declLocal .uint (.user "x")
    (some (.binop .add rfl rfl (.read (.field alice "age" rfl)) (lit 1)))) <|
  .cons (.declStorage P (.user "p") (some (.path alice))) <|
  .cons (.assign (.field (.alias .here) "age" rfl) (.val (loc (.there .here)))) <|
  .cons (.ite (.binop .gt rfl rfl (loc (.there .here)) (lit 3))
    (.cons (.declLocal .uint (.user "y") (some (loc (.there .here)))) <|
      .cons (.assign (.field alice "age" rfl) (.val (loc .here))) .nil)
    (.cons .revert .nil)) <|
  .cons (.block (.cons (.declLocal .uint (.user "z") (some (lit 2))) <|
    .cons (.assign (.index .map (.loc (.root "balances" rfl)) (loc .here))
      (.val (loc (.there (.there .here))))) .nil)) <|
  .cons (.call "f" ((Args.nil.snoc .uint (.user "a") (loc (.there .here))).snoc .uint (.user "b")
      (lit 1)) (.val .uint (.user "r") (some (.there .here))) .nil) <|
  .cons (.call "g" .nil (.mem P (.user "r") rfl rfl) .nil) <|
  .cons (.declMem P (.user "m") (some (.alias (.var .here rfl))) rfl rfl) <|
  .cons (.call "h" .nil (.rets ((Binders.nil.snoc .uint (.user "r0")).snoc .uint (.user "r1")))
    .nil) <|
  .cons (.assignLocal (.there (.there (.there (.there (.there .here))))) (loc .here)) <|
  .cons (.tryCall ⟨.local (.there (.there (.there (.there (.there .here))))), "ping",
      [⟨.uint, .local .here⟩]⟩ (Binders.nil.snoc .uint (.user "v"))
    (.cons (.assignLocal (.there (.there (.there (.there (.there (.there .here)))))) (loc .here))
      .nil)
    .nil (.some (.user "c")) .nil (.cons .revert .nil)) .nil

/--
info: uint x = alice.age + 1;
Person storage p = alice;
p.age = x;
if (x > 3) { uint y = x; alice.age = y; } else { revert(); }
{ uint z = 2; balances[z] = x; }
x = f(x, 1);
Person memory m = g();
(, x) = h();
try address(x).ping(r1) returns (uint v) { x = v; } catch Error(string memory) { } catch Panic(uint c) { } catch { revert(); }
-/
#guard_msgs in #eval IO.println (Prog.show [] example₁)

/-- `x = x + 1; uint y = x;`, reading the local `x` it is given. -/
private def example₂ : Prog SE [.val .uint] [.val .uint, .val .uint] :=
  .cons (.assignLocal .here (.binop .add rfl rfl (loc .here) (lit 1))) <|
  .cons (.declLocal .uint (.user "y") (some (loc .here))) .nil

-- Weakened under a local `w` declared after `x`, it still reads `x`.
#guard Prog.toStr [.user "w", .user "x"] (example₂.wk (.drop (t := .val .bool) .refl)).2.2 =
  "x = x + 1; uint y = x;"

-- A block weakened under one more local reads the same locals.
#guard Prog.toStr [.user "w"] (example₁.wk (.drop (t := .val .bool) .refl)).2.2 =
  Prog.toStr [] example₁

end Example

end Solidity.Core
