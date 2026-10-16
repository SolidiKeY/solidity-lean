import Solidity.Update
import Solidity.Semantics.Run
import Solidity.Semantics.StorageWt
import Solidity.Theory.Typed.Obs

/-!
# KeY's signature, typed

KeY's sorts indexed by Solidity types (`Srt`: `val p`, `path T`, `st`,
`sv T`, `ident R`, `addr T`, `mem`, `mv T`, and under `select` `sts s`,
`spath s T`), and the symbols over the contract (`Op0` … `Op3`), each read
on the typed global part (`State C []`, `State.glob`) by the typed
operations of `Semantics/Storage.lean`, `Semantics/Heap.lean` and
`Semantics/Run.lean`: `OpN.eval`, where a revert is `none` and nothing is
`undef`.  The terms over them are `Calculus/Fml.lean`'s (W9.8.3: the
untyped signature of `Update.lean` and its bridge are gone,
`docs/intrinsic.md`).

**What the sorts denote** (`Srt.Den C H`, over the heap typing `H` of the
global part): a value of its type, a storage reference `SRef C T`, a
storage `Storage C`, a storage value `SVal T`; a memory a heap grown from
`H` (`Grown H`: `addM`/`copySt` extend it); an identity a bare `Nat` and an
address its `MAddrT`, checked against the typing of the memory they are
read in (`HRef.ofId?`), since a fresh identity's type is not static.

**Symbols.**  `netOf` is a local's (`Tm.netOf`, `Calculus/Fml.lean`).
`select(s, r)` reads at its own sorts: `sts s`, the struct `s`'s members
read as a storage (`Storage (Contract.ofStruct s)`), and `spath s T`, a
path from one of them; `select` from the storage at a root, `selectIn`
from an `sts` at a member, and `member`/`fieldIn`/`findIn`/`sfindIn`/
`delAtIn`/`saveIn` the symbols under it.  An index (`at`, `atIn`) takes
a value of its key type: a mapping's key, an array's `uint` index.

The evaluators are kernel-evaluated: each is a `casesOn` with a `match`
twin as its `implemented_by` and a link theorem (Gate G0).
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## Sorts -/

/-- KeY's sorts (`Srt`), indexed by Solidity types. -/
inductive Srt where
  /-- `Term` at a primitive type. -/
  | val (p : PrimTy)
  /-- `PTerm` to a `T`. -/
  | path (T : Ty)
  /-- `STerm`. -/
  | st
  /-- `SValT` of type `T`. -/
  | sv (T : Ty)
  /-- `ITerm`: an object of type `R`. -/
  | ident (R : RefTy)
  /-- `MAddr` of a slot of type `T`. -/
  | addr (T : Ty)
  /-- `MTerm`. -/
  | mem
  /-- `MValT` of type `T`. -/
  | mv (T : Ty)
  /-- `STerm` at a struct's members: `select(s, r)`, the struct `s` read as
  a storage whose roots are its members (`Contract.ofStruct`). -/
  | sts (s : Name)
  /-- `PTerm` under `select`: from a member of the struct `s` to a `T`. -/
  | spath (s : Name) (T : Ty)
  /-- KeY's `int`: an unbounded integer, apart from Solidity's `int256`
  (`val .int`).  The ledger's entries (`net(a)`, `x[a]`), `msg.value` and a
  `uint` widened (`toInt`), and a specification's arithmetic over them are
  KeY `int`s (solkey's `netHeader.key`, `SpecCompiler`): total, unbounded. -/
  | kint
  deriving DecidableEq, Repr

/-- An operator KeY's `int` has, unbounded: `+`, `-`, `*`. -/
def BinOp.zArith : BinOp → Bool
  | .add | .sub | .mul => true
  | _ => false

/-- A comparison of two KeY `int`s: `<`, `>`, `<=`, `>=`, `==`, `!=`. -/
def BinOp.zCmp : BinOp → Bool
  | .lt | .gt | .le | .ge | .eqB | .neB => true
  | _ => false

/-- `a ⊕ b` on KeY's `int`, unbounded (`0` off `zArith`). -/
def BinOp.evalZ : BinOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | _, _, _ => 0

/-- `a ⊲ b` on KeY's `int` (`false` off `zCmp`). -/
def BinOp.cmpZ : BinOp → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .gt, a, b => decide (b < a)
  | .le, a, b => decide (a ≤ b)
  | .ge, a, b => decide (b ≤ a)
  | .eqB, a, b => decide (a = b)
  | .neB, a, b => !decide (a = b)
  | _, _, _ => false

/-! ## Identities and addresses -/

/-- An identity of an `R` in the heap typing `H`: `none` off it. -/
def HRef.ofId? (H : HTy) (R : RefTy) (id : Nat) : Option (HRef H R) :=
  if h : H[id]? = some R then some ⟨id, h⟩ else none

/-- A memory address (`MAddr`), its identity unchecked. -/
inductive MAddrT : Ty → Type where
  | field {s f : Name} {T : Ty} (id : Nat) (h : lookupBy f (structDef s) = some T) : MAddrT T
  | index {R : RefTy} {E : Ty} (id : Nat) (a : ArrTy R E) (i : PrimTy.uint.Denote) : MAddrT E

/-- `resolve` by `match`, its compiled form. -/
def MAddrT.resolveM (H : HTy) {T : Ty} : MAddrT T → Option (MAddr H T)
  | @MAddrT.field s _ _ id h => (HRef.ofId? H (.struct s) id).map (MAddr.field · h)
  | @MAddrT.index R _ id a i => (HRef.ofId? H R id).map (MAddr.index · a i)

/-- The address in the heap typing `H`: `none` where its identity is not
an object of its type there. -/
@[implemented_by MAddrT.resolveM]
def MAddrT.resolve (H : HTy) {T : Ty} (a : MAddrT T) : Option (MAddr H T) :=
  @MAddrT.casesOn (fun T _ => Option (MAddr H T)) T a
    (fun {s} {_} {_} id h => (HRef.ofId? H (.struct s) id).map (MAddr.field · h))
    (fun {R} {_} id a i => (HRef.ofId? H R id).map (MAddr.index · a i))

theorem MAddrT.resolve_eq_resolveM (H : HTy) {T : Ty} (a : MAddrT T) :
    a.resolve H = a.resolveM H := by
  cases a <;> rfl

/-- What a memory write writes at a `T`: a word, or an identity. -/
@[reducible] def MvT : Ty → Type
  | .prim p => p.Denote
  | .ref _ => Nat

/-- The slot value over the heap typing `H`. -/
def MvT.toMVal (H : HTy) : (T : Ty) → MvT T → Option (MVal H T)
  | .prim _, v => some v
  | .ref R, id => HRef.ofId? H R id

/-! ## What the sorts denote -/


/-- A typed sort's values, over the global part's heap typing `H`. -/
@[reducible] def Srt.Den (C : Contract) (H : HTy) : Srt → Type
  | .val p => p.Denote
  | .path T => SRef C T
  | .st => Storage C
  | .sv T => SVal T
  | .ident _ => Nat
  | .addr T => MAddrT T
  | .mem => Grown H (fun _ => Unit)
  | .mv T => MvT T
  | .sts s => Storage (Contract.ofStruct s)
  | .spath s T => SRef (Contract.ofStruct s) T
  | .kint => Int

/-- The memory as it is: the heap grown by nothing. -/
def State.memT (g : State C []) : Grown g.H (fun _ => Unit) := ⟨List.prefix_refl _, g.heap, ()⟩

/-! ## Symbols -/

/-- Constants. -/
inductive Op0 (C : Contract) : Srt → Type where
  | lit {p : PrimTy} (v : p.Denote) : Op0 C (.val p)
  | env (k : EnvKey) : Op0 C (.val .uint)
  | root (r : Name) {T : Ty} (h : C.rootType r = some T) : Op0 C (.path T)
  | storage : Op0 C .st
  | memory : Op0 C .mem
  /-- `mtSt`: every root of the contract at its default (`Storage.init`). -/
  | mtSt : Op0 C .st
  /-- A member `f` of the struct `s` as a root under `select` (`Op0.root f`). -/
  | member (s f : Name) {T : Ty} (h : C.fieldType s f = some T) : Op0 C (.spath s T)
  /-- A KeY `int` literal. -/
  | zlit (n : Int) : Op0 C .kint

/-- Unary symbols. -/
inductive Op1 (C : Contract) : Srt → Srt → Type where
  | unop (op : UnOp) {p : PrimTy} (h : op.accepts p = true) : Op1 C (.val p) (.val (op.ret p))
  /-- `net(a)`: the ledger's entry, a KeY `int`. -/
  | net : Op1 C (.val .uint) .kint
  | delValue {p : PrimTy} : Op1 C (.val p) (.val p)
  | field {s f : Name} {T : Ty} (h : C.fieldType s f = some T) :
      Op1 C (.path (.ref (.struct s))) (.path T)
  | next {E : Ty} : Op1 C (.path (.ref (.array E))) (.path E)
  | sval {p : PrimTy} : Op1 C (.val p) (.sv (.prim p))
  | newArr {R : RefTy} (h : R.newArrOk = true) : Op1 C (.val .uint) (.sv (.ref R))
  | alloc (R : RefTy) (h : (Ty.ref R).mapFree = true) : Op1 C .mem (.ident R)
  | mfield {s f : Name} {T : Ty} (h : C.fieldType s f = some T) :
      Op1 C (.ident (.struct s)) (.addr T)
  | addM (R : RefTy) (h : (Ty.ref R).mapFree = true) : Op1 C .mem .mem
  | mval {p : PrimTy} : Op1 C (.val p) (.mv (.prim p))
  | ref {R : RefTy} : Op1 C (.ident R) (.mv (.ref R))
  | wt : Op1 C .st (.val .bool)
  /-- `select(s, r)`: the struct at the root `r`, read as a storage of its
  members (KeY's `selectSt<[Struct]>(s, r)`). -/
  | select {s : Name} (r : Name) (h : C.rootType r = some (.ref (.struct s))) :
      Op1 C .st (.sts s)
  /-- `select(s, f)` under a `select`: the struct at the member `f`. -/
  | selectIn {s s' f : Name} (h : C.fieldType s f = some (.ref (.struct s'))) :
      Op1 C (.sts s) (.sts s')
  /-- `p.f` under a `select`. -/
  | fieldIn {s s' f : Name} {T : Ty} (h : C.fieldType s' f = some T) :
      Op1 C (.spath s (.ref (.struct s'))) (.spath s T)
  /-- A `uint` read as a KeY `int`: KeY has one `int` sort, so solkey writes
  nothing (its `msgValue` and the ledger's entries are `int`s, `netHeader.key`);
  a specification's `net(a) + msg.value` reads `msg.value` so.  Total. -/
  | toInt : Op1 C (.val .uint) .kint
  /-- The typed view of a fixed-array copy source at its destination shape. -/
  | fixedCopy {E : Ty} {n : Nat} {R : RefTy} (shape : FixedCopy E n R) :
      Op1 C (.sv (.ref (.fixed E n))) (.sv (.ref R))

/-- Binary symbols. -/
inductive Op2 (C : Contract) : Srt → Srt → Srt → Type where
  | binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true) :
      Op2 C (.val p) (.val p) (.val (op.ret p))
  | find {p : PrimTy} : Op2 C .st (.path (.prim p)) (.val p)
  | len {E : Ty} : Op2 C .st (.path (.ref (.array E))) (.val .uint)
  | read {p : PrimTy} : Op2 C .mem (.addr (.prim p)) (.val p)
  | mlen {E : Ty} : Op2 C .mem (.ident (.array E)) (.val .uint)
  | at {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) :
      Op2 C (.path (.ref R)) (.val k) (.path V)
  | nextIn {E : Ty} : Op2 C .st (.path (.ref (.array E))) (.path E)
  | delAt {T : Ty} : Op2 C .st (.path T) .st
  | pushSlot {E : Ty} : Op2 C .st (.path (.ref (.array E))) .st
  | pop {E : Ty} : Op2 C .st (.path (.ref (.array E))) .st
  | shrink {E : Ty} : Op2 C .st (.path (.ref (.array E))) .st
  | extend {E : Ty} : Op2 C .st (.path (.ref (.array E))) .st
  | sfind {T : Ty} : Op2 C .st (.path T) (.sv T)
  | copyMem {R : RefTy} : Op2 C .mem (.ident R) (.sv (.ref R))
  | iread {R : RefTy} : Op2 C .mem (.addr (.ref R)) (.ident R)
  | copy {R : RefTy} (h : (Ty.ref R).mapFree = true) : Op2 C .mem (.sv (.ref R)) (.ident R)
  | mat {R : RefTy} {E : Ty} (a : ArrTy R E) : Op2 C (.ident R) (.val .uint) (.addr E)
  | copySt {T : Ty} (h : T.mapFree = true) : Op2 C .mem (.sv T) .mem
  /-- `find(s, p)` under a `select`. -/
  | findIn {s : Name} {p : PrimTy} : Op2 C (.sts s) (.spath s (.prim p)) (.val p)
  /-- `delAt(s, p)` under a `select`. -/
  | delAtIn {s : Name} {T : Ty} : Op2 C (.sts s) (.spath s T) (.sts s)
  /-- `sfind(s, p)` under a `select`. -/
  | sfindIn {s : Name} {T : Ty} : Op2 C (.sts s) (.spath s T) (.sv T)
  /-- `a + b`, `a - b`, `a * b` on KeY's `int`, unbounded. -/
  | zbin (op : BinOp) (h : op.zArith = true) : Op2 C .kint .kint .kint
  /-- `a < b`, …, `a == b` on KeY's `int`. -/
  | zcmp (op : BinOp) (h : op.zCmp = true) : Op2 C .kint .kint (.val .bool)

/-- Ternary symbols. -/
inductive Op3 (C : Contract) : Srt → Srt → Srt → Srt → Type where
  | ite {p : PrimTy} : Op3 C (.val .bool) (.val p) (.val p) (.val p)
  | save {T : Ty} : Op3 C .st (.path T) (.sv T) .st
  | push {E : Ty} : Op3 C .st (.path (.ref (.array E))) (.sv E) .st
  | atIn {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) :
      Op3 C .st (.path (.ref R)) (.val k) (.path V)
  | write {T : Ty} : Op3 C .mem (.addr T) (.mv T) .mem
  /-- `save(s, p, v)` under a `select`. -/
  | saveIn {s : Name} {T : Ty} : Op3 C (.sts s) (.spath s T) (.sv T) (.sts s)
  /-- Native modular arithmetic, with an unbounded intermediate. -/
  | modular (op : ModOp) : Op3 C (.val .uint) (.val .uint) (.val .uint) (.val .uint)


/-! ## Evaluation on the typed global part

An argument comes as an `Option`, as `Update.lean`'s comes as a `Res`: `&&`,
`||` and `c ? a : b` do not read the operand they do not need. -/

/-- A grown heap grown further. -/
def Grown.then {H : HTy} {α : HTy → Type} (m : Grown H (fun _ => Unit)) (n : Grown m.H' α) :
    Grown H (fun _ => Unit) :=
  ⟨m.ext.trans n.ext, n.heap, ()⟩

/-- `wt(storage)`: `true` on a storage passing the test (`Storage.wtB`,
`Semantics/StorageWt.lean`), undefined on any other. -/
def Storage.wtT (st : Storage C) : Option PrimTy.bool.Denote :=
  if st.wtB then some (true : Bool) else none

/-- `p[p.length]` in `st`: the slot past the live elements. -/
def Storage.nextT {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) : Option (SRef C E) :=
  (st.find r).map fun (v : SVal (.ref (.array E))) =>
    let w : ArrView E := SVal.view v
    r.index (.arr .dyn) (lenU w.n w.hn)

/-- `p[i]` with its index checked in `st`. -/
def Storage.atT {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C) (it : IndexTy R k V)
    (r : SRef C (.ref R)) (i : k.Denote) : Option (SRef C V) := do
  st.checkIndex r it i
  some (r.index it i)


/-- `Op0.eval` by `match`, its compiled form. -/
def Op0.evalM (g : State C []) {s : Srt} : Op0 C s → Option (s.Den C g.H)
  | .lit v => some v
  | .env k => some (g.envVal k)
  | .root r h => some (SRef.ofRoot r h)
  | .storage => some g.storage
  | .memory => some g.memT
  | .mtSt => some (Storage.init C)
  | .member _ f h => some (SRef.ofRoot (C := Contract.ofStruct _) f h)
  | .zlit n => some n

/-- A constant on the typed global part. -/
@[implemented_by Op0.evalM]
def Op0.eval (g : State C []) {s : Srt} (o : Op0 C s) : Option (s.Den C g.H) :=
  @Op0.casesOn C (fun s _ => Option (s.Den C g.H)) s o
    (fun {_} v => some v) (fun k => some (g.envVal k)) (fun r {_} h => some (SRef.ofRoot r h))
    (some g.storage) (some g.memT) (some (Storage.init C))
    (fun _ f {_} h => some (SRef.ofRoot (C := Contract.ofStruct _) f h))
    (fun n => some n)

theorem Op0.eval_eq_evalM (g : State C []) {s : Srt} (o : Op0 C s) : o.eval g = o.evalM g := by
  cases o <;> rfl

/-- `Op1.eval` by `match`, its compiled form. -/
def Op1.evalM (g : State C []) {a s : Srt} :
    Op1 C a s → Option (a.Den C g.H) → Option (s.Den C g.H)
  | .unop op h, x => x.bind (op.evalT h)
  | .net, x => x.map fun n => (lookupBy n g.net).getD 0
  | .delValue, x => x.map fun _ => PrimTy.dflt _
  | .field h, x => x.map (·.field h)
  | .next, x => x.bind g.storage.nextT
  | .sval, x => x.map .prim
  | .newArr h, x => x.map fun n => newArrT _ n h
  | .alloc R h, x => x.map fun m => (m.heap.allocDefault R h).val.id
  | .mfield h, x => x.map fun id => .field id h
  | .addM R h, x => x.map fun m => m.then (m.heap.allocDefault R h)
  | .mval, x => x
  | .ref, x => x
  | .wt, x => x.bind Storage.wtT
  | .select _ h, x => x.map fun st => Storage.selectT st h
  | .selectIn h, x => x.map fun st => Storage.selectT (C := Contract.ofStruct _) st h
  | .fieldIn h, x => x.map (SRef.field · h)
  | .toInt, x => x.map fun n => n.1
  | .fixedCopy shape, x => x.map shape.apply

/-- A unary symbol on the typed global part. -/
@[implemented_by Op1.evalM]
def Op1.eval (g : State C []) {a s : Srt} (o : Op1 C a s) :
    Option (a.Den C g.H) → Option (s.Den C g.H) :=
  @Op1.casesOn C (fun a s _ => Option (a.Den C g.H) → Option (s.Den C g.H)) a s o
    (fun op {_} h x => x.bind (op.evalT h))
    (fun x => x.map fun n => (lookupBy n g.net).getD 0)
    (fun {_} x => x.map fun _ => PrimTy.dflt _)
    (fun {_} {_} {_} h x => x.map (·.field h))
    (fun {_} x => x.bind g.storage.nextT)
    (fun {_} x => x.map .prim)
    (fun {_} h x => x.map fun n => newArrT _ n h)
    (fun R h x => x.map fun m => (m.heap.allocDefault R h).val.id)
    (fun {_} {_} {_} h x => x.map fun id => .field id h)
    (fun R h x => x.map fun m => m.then (m.heap.allocDefault R h))
    (fun {_} x => x)
    (fun {_} x => x)
    (fun x => x.bind Storage.wtT)
    (fun {_} _ h x => x.map fun st => Storage.selectT st h)
    (fun {_} {_} {_} h x => x.map fun st => Storage.selectT (C := Contract.ofStruct _) st h)
    (fun {_} {_} {_} {_} h x => x.map (SRef.field · h))
    (fun x => x.map fun n => n.1)
    (fun {_} {_} {_} shape x => x.map shape.apply)

theorem Op1.eval_eq_evalM (g : State C []) {a s : Srt} (o : Op1 C a s) :
    o.eval g = o.evalM g := by
  cases o <;> rfl

/-- `a ⊕ b`: `&&`/`||` decided by `a` alone (`BinOp.shortT`), else both. -/
def binopT (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (a : p.Denote)
    (y : Option p.Denote) :
    Option (op.ret p).Denote :=
  match op.shortT a with
  | some r => some r
  | none => y.bind (op.evalT h a)

/-- `read(m, a)`: the slot at `a` in `m`. -/
def Grown.readT {H : HTy} {T : Ty} (m : Grown H (fun _ => Unit)) (a : MAddrT T) :
    Option (MVal m.H' T) := do
  m.heap.readAddr (← a.resolve m.H')

/-- `write(m, a, v)`. -/
def Grown.writeT {H : HTy} {T : Ty} (m : Grown H (fun _ => Unit)) (a : MAddrT T) (v : MvT T) :
    Option (Grown H (fun _ => Unit)) := do
  let hp ← m.heap.writeAddr (← a.resolve m.H') (← MvT.toMVal m.H' T v)
  some ⟨m.ext, hp, ()⟩

/-- `Op2.eval` by `match`, its compiled form. -/
def Op2.evalM (g : State C []) {a b s : Srt} :
    Op2 C a b s → Option (a.Den C g.H) → Option (b.Den C g.H) → Option (s.Den C g.H)
  | .binop op h, x, y => x.bind fun a => binopT op h a y
  | .find, x, y => do let v ← (← x).find (← y); some v.view
  | .len, x, y => do (← x).len (← y)
  | .read, x, y => do (← x).readT (← y)
  | @Op2.mlen _ E, x, y => do
    let m ← x
    some (m.heap.lenU (← HRef.ofId? m.H' (.array E) (← y)))
  | .at it, x, y => do g.storage.atT it (← x) (← y)
  | .nextIn, x, y => do (← x).nextT (← y)
  | .delAt, x, y => do (← x).delete (← y)
  | .pushSlot, x, y => do (← x).push (← y) some
  | .pop, x, y => do (← x).pop false (← y)
  | .shrink, x, y => do (← x).pop true (← y)
  | .extend, x, y => do some ((← (← x).extendPlace (← y)).1)
  | .sfind, x, y => do (← x).find (← y)
  | .copyMem, x, y => do
    let m ← x
    some (MVal.copyMToSt m.heap (T := .ref _) (← HRef.ofId? m.H' _ (← y)))
  | .iread, x, y => do
    let r : HRef _ _ ← (← x).readT (← y)
    some r.id
  | .copy h, x, y => do
    let m ← x
    let r : HRef _ _ := ((← y).copyStToM m.heap h).val
    some r.id
  | .mat a, x, y => do some (.index (← x) a (← y))
  | .copySt h, x, y => do
    let m ← x
    some (m.then ((← y).copyStToM m.heap h))
  | .findIn, x, y => do let v ← (← x).find (← y); some v.view
  | .delAtIn, x, y => do (← x).delete (← y)
  | .sfindIn, x, y => do (← x).find (← y)
  | .zbin op _, x, y => do some (op.evalZ (← x) (← y))
  | .zcmp op _, x, y => do some (op.cmpZ (← x) (← y))

/-- A binary symbol on the typed global part. -/
@[implemented_by Op2.evalM]
def Op2.eval (g : State C []) {a b s : Srt} (o : Op2 C a b s) :
    Option (a.Den C g.H) → Option (b.Den C g.H) → Option (s.Den C g.H) :=
  @Op2.casesOn C
    (fun a b s _ => Option (a.Den C g.H) → Option (b.Den C g.H) → Option (s.Den C g.H)) a b s o
    (fun op {_} h x y => x.bind fun a => binopT op h a y)
    (fun {_} x y => do let v ← (← x).find (← y); some v.view)
    (fun {_} x y => do (← x).len (← y))
    (fun {_} x y => do (← x).readT (← y))
    (fun {E} x y => do
      let m ← x
      some (m.heap.lenU (← HRef.ofId? m.H' (.array E) (← y))))
    (fun {_} {_} {_} it x y => do g.storage.atT it (← x) (← y))
    (fun {_} x y => do (← x).nextT (← y))
    (fun {_} x y => do (← x).delete (← y))
    (fun {_} x y => do (← x).push (← y) some)
    (fun {_} x y => do (← x).pop false (← y))
    (fun {_} x y => do (← x).pop true (← y))
    (fun {_} x y => do some ((← (← x).extendPlace (← y)).1))
    (fun {_} x y => do (← x).find (← y))
    (fun {_} x y => do
      let m ← x
      some (MVal.copyMToSt m.heap (T := .ref _) (← HRef.ofId? m.H' _ (← y))))
    (fun {_} x y => do
      let r : HRef _ _ ← (← x).readT (← y)
      some r.id)
    (fun {_} h x y => do
      let m ← x
      let r : HRef _ _ := ((← y).copyStToM m.heap h).val
      some r.id)
    (fun {_} {_} a x y => do some (.index (← x) a (← y)))
    (fun {_} h x y => do
      let m ← x
      some (m.then ((← y).copyStToM m.heap h)))
    (fun {_} {_} x y => do let v ← (← x).find (← y); some v.view)
    (fun {_} {_} x y => do (← x).delete (← y))
    (fun {_} {_} x y => do (← x).find (← y))
    (fun op _ x y => do some (op.evalZ (← x) (← y)))
    (fun op _ x y => do some (op.cmpZ (← x) (← y)))

theorem Op2.eval_eq_evalM (g : State C []) {a b s : Srt} (o : Op2 C a b s) :
    o.eval g = o.evalM g := by
  cases o <;> rfl

/-- `Op3.eval` by `match`, its compiled form. -/
def Op3.evalM (g : State C []) {a b c s : Srt} :
    Op3 C a b c s → Option (a.Den C g.H) → Option (b.Den C g.H) → Option (c.Den C g.H) →
      Option (s.Den C g.H)
  | .ite, x, y, z => x.bind fun c => cond c y z
  | .save, x, y, z => do (← x).write (← y) (← z)
  | .push, x, y, z => do (← x).push (← y) fun _ => z.map SVal.strip
  | .atIn it, x, y, z => do (← x).atT it (← y) (← z)
  | .write, x, y, z => do (← x).writeT (← y) (← z)
  | .saveIn, x, y, z => do (← x).write (← y) (← z)
  | .modular op, x, y, z => do op.evalT (← x) (← y) (← z)

/-- A ternary symbol on the typed global part. -/
@[implemented_by Op3.evalM]
def Op3.eval (g : State C []) {a b c s : Srt} (o : Op3 C a b c s) :
    Option (a.Den C g.H) → Option (b.Den C g.H) → Option (c.Den C g.H) → Option (s.Den C g.H) :=
  @Op3.casesOn C (fun a b c s _ => Option (a.Den C g.H) → Option (b.Den C g.H) →
      Option (c.Den C g.H) → Option (s.Den C g.H)) a b c s o
    (fun {_} x y z => x.bind fun c => cond c y z)
    (fun {_} x y z => do (← x).write (← y) (← z))
    (fun {_} x y z => do (← x).push (← y) fun _ => z.map SVal.strip)
    (fun {_} {_} {_} it x y z => do (← x).atT it (← y) (← z))
    (fun {_} x y z => do (← x).writeT (← y) (← z))
    (fun {_} {_} x y z => do (← x).write (← y) (← z))
    (fun op x y z => do op.evalT (← x) (← y) (← z))

theorem Op3.eval_eq_evalM (g : State C []) {a b c s : Srt} (o : Op3 C a b c s) :
    o.eval g = o.evalM g := by
  cases o <;> rfl




theorem binopT_some (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (a b : p.Denote) :
    binopT op h a (some b) = op.evalT h a b := by
  unfold binopT
  cases op <;> cases p <;> (try cases a) <;> rfl

theorem Storage.push_none {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) :
    st.push r (fun _ => none) = none := by
  unfold Storage.push
  cases st.find r <;> rfl

/-! ## The laws, typed

solkey's `selectOnSaveCons`, its `\then` and its `\else`, as the laws
`findOnSave` and `findOnSaveFrame` (`TermTaclet.findOnSave`,
`TermTaclet.findOnSaveFrame`) on the typed storage, where the write lands
(the typed Theory's `Obs.findOnSave` and `Obs.findOnSaveFrame`,
`Theory/Typed/Obs.lean`, need no premise: KeY's model is total).  A typed `save` is the program's
write (`Storage.write`: a word stored, a struct or an array laid over what is
there), which is a `Storage.save` at the same reference. -/

namespace Storage

/-- `save`'s landing as a storage write: the root's value saved below. -/
theorem save_some {U : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    (h : st.save r v = some st') :
    ∃ x', (st.get r.hroot).save r.path v = some x' ∧ st' = st.set r.hroot x' := by
  unfold Storage.save at h
  cases hs : (st.get r.hroot).save r.path v with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some x' =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
    exact ⟨x', rfl, h.symm⟩

/-- A write is a save at its reference. -/
theorem write_some {U : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    (h : st.write r v = some st') : ∃ w, st.save r w = some st' := by
  unfold Storage.write at h
  split at h
  · exact ⟨v, h⟩
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨cur, _, h⟩ := h
    exact ⟨_, h⟩

/-- **`findOnSave`**, typed: a word written where the write lands reads back
(solkey's `selectOnSaveCons` `\then`; Theory `Obs.findOnSave`). -/
theorem findOnSave {p : PrimTy} (st : Storage C) (r : SRef C (.prim p)) (v : p.Denote)
    {st' : Storage C} (h : st.write r (.prim v) = some st') : st'.find r = some (.prim v) := by
  obtain ⟨x', hs, rfl⟩ := save_some (show st.save r (.prim v) = some st' from h)
  simp only [Storage.find, SFields.get_set_same]
  exact SVal.find_save_same _ _ _ hs

/-- **`findOnSaveFrame`** across roots, typed: a write leaves another state
variable as it was (solkey's `selectOnSaveCons` `\else`; Theory
`Obs.findOnSaveFrame`). -/
theorem findOnSaveFrameRoot {U W : Ty} (st : Storage C) (r : SRef C U) (q : SRef C W)
    (hne : r.root ≠ q.root) (v : SVal U) {st' : Storage C} (h : st.write r v = some st') :
    st'.find q = st.find q := by
  obtain ⟨w, hw⟩ := write_some h
  obtain ⟨x', _, rfl⟩ := save_some hw
  simp only [Storage.find, SFields.get_set_ne _ r.hroot q.hroot hne]

/-! ### Under `select`

A path under `select(s, r)` is a path from `r`'s member: `SRef.under`.
The laws above are over any contract, so over `Contract.ofStruct s` they
are the laws of `sts s` (`findOnSave (C := Contract.ofStruct s)`, …). -/

/-- **`findMemberCons`**, typed: a read under `select(s, r)` is the read at
`r` followed by its path (Theory `Obs.select_find`). -/
theorem find_selectT {s r : Name} {U : Ty} (st : Storage C)
    (h : C.rootType r = some (.ref (.struct s))) (q : SRef (Contract.ofStruct s) U) :
    (st.selectT h).find q = st.find (q.under h) := by
  simp only [Storage.find, Storage.selectT, SRef.under]
  generalize st.get h = w
  cases w
  rfl

end Storage

end Solidity
