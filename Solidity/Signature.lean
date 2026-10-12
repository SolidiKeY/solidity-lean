import Solidity.Update
import Solidity.Semantics.TypedErase
import Solidity.Semantics.StorageErase
import Solidity.Theory.StateWrites

/-!
# KeY's signature, typed

The sorts of `Update.lean` indexed by Solidity types (`SrtT`: `val p`,
`path T`, `st`, `sv T`, `ident R`, `addr T`, `mem`, `mv T`), and the
symbols over the contract (`OpT0` … `OpT3`), each read on the typed global
part (`State C []`, `State.glob`) by the typed operations of
`Semantics/Storage.lean`, `Semantics/Heap.lean` and `Semantics/Run.lean`:
`OpTn.eval`, where a revert is `none` and nothing is `undef`.  It is the
signature W9.8 moves the terms to (`docs/intrinsic.md`, "W9.8 plan"); the
name stays when `Update.lean`'s untyped one goes.

**What the sorts denote** (`SrtT.Den C H`, over the heap typing `H` of the
global part): a value of its type, a storage reference `SRef C T`, a
storage `Storage C`, a storage value `SVal T`; a memory a heap grown from
`H` (`Grown H`: `addM`/`copySt` extend it); an identity a bare `Nat` and an
address its `MAddrT`, checked against the typing of the memory they are
read in (`HRef.ofId?`), since a fresh identity's type is not static.

**Symbols.**  Every symbol of `Op0` … `Op3` has a typed one of the same
name, but two:
- `Op1.netOf` is a local's (`TmT.netOf`, `Calculus/TypedTerm.lean`), as it
  is `Tm.netOf`;
- `Op1.select` (`select(s, r)`, a line of a chain's read taken head first)
  has none: a struct's members read as a storage are not a `Storage C`.
  Its typed reading is `sfind(s, r)` (W9.8.2 decides the chain lines).
An index (`at`, `atIn`) takes the word its key is hashed as, at
`PrimTy.keyTy` (a `bool` key at `uint`), as `Tm.keyAt` writes it.

**The bridge** (`OpTn.erase`, `OpTn.eval_agree`): a typed symbol erases to
its untyped namesake, and on the erased global part (`State.globE`) the
untyped evaluation agrees with the typed one (`SrtT.Agree`: `some x` reads
`.ok` of `x` erased, `none` some halt; the halt's kind is not kept: `Res`'s
`revert` and `panic` are both `none`).  It is exact where the typed symbol
is (`OpTn.Exact`), everywhere but:
- a memory read or write through an identity (`read`, `iread`, `mlen`,
  `copyMem`, `write`): the identity must have its type in the memory read
  (`IdOk`); the untyped read takes any object with the member;
- a push onto a full array (`pushSlot`, `extend`, `push`): the typed one is
  `none`, out of gas (`Storage.full`), the untyped one writes;
- `net(a)`: the entry must be an `int` (the ledger is unbounded).
The untyped symbols' kernel forms are kept: the twin-then-switch of W9.8
reads its laws across this bridge.

The evaluators are kernel-evaluated: each is a `casesOn` with a `match`
twin as its `implemented_by` and a link theorem (Gate G0); the bridge is
proved on the twin.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## Sorts -/

/-- KeY's sorts (`Srt`), indexed by Solidity types. -/
inductive SrtT where
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
  deriving DecidableEq, Repr

/-- The untyped sort (the printer's, the sort check's). -/
def SrtT.erase : SrtT → Srt
  | .val _ => .val
  | .path _ => .path
  | .st => .st
  | .sv _ => .sv
  | .ident _ => .ident
  | .addr _ => .addr
  | .mem => .mem
  | .mv _ => .mv

/-- The type an index of key type `k` is hashed at: a `bool` key is the
word `0` or `1` (`Tm.keyAt`). -/
def PrimTy.keyTy : PrimTy → PrimTy
  | .bool => .uint
  | .uint => .uint
  | .int => .int

/-- An index's word is the integer the untyped interpreter reads. -/
theorem PrimTy.asInt_erase_keyTy : (k : PrimTy) → (i : k.keyTy.Denote) →
    (PrimTy.erase i).asInt = .ok (PrimTy.key i)
  | .bool, _ | .uint, _ | .int, _ => rfl

/-! ## Identities and addresses -/

/-- An identity of an `R` in the heap typing `H`: `none` off it. -/
def HRef.ofId? (H : HTy) (R : RefTy) (id : Nat) : Option (HRef H R) :=
  if h : H[id]? = some R then some ⟨id, h⟩ else none

/-- The identity `id` names an `R` in `H`: where a typed memory read is exact. -/
def IdOk (H : HTy) (R : RefTy) (id : Nat) : Prop := H[id]? = some R

theorem HRef.ofId?_of_ok {H : HTy} {R : RefTy} {id : Nat} (h : IdOk H R id) :
    HRef.ofId? H R id = some ⟨id, h⟩ := dif_pos h

/-- A memory address (`MAddr`), its identity unchecked. -/
inductive MAddrT : Ty → Type where
  | field {s f : Name} {T : Ty} (id : Nat) (h : lookupBy f (structDef s) = some T) : MAddrT T
  | index {R : RefTy} {E : Ty} (id : Nat) (a : ArrTy R E) (i : Int) : MAddrT E

/-- The untyped address. -/
def MAddrT.erase {T : Ty} : MAddrT T → Addr
  | @MAddrT.field _ f _ id _ => .memoryField id f
  | .index id _ i => .memoryIndex id i

/-- Its identity names the object it addresses in `H`. -/
def MAddrT.Ok (H : HTy) {T : Ty} : MAddrT T → Prop
  | @MAddrT.field s _ _ id _ => IdOk H (.struct s) id
  | @MAddrT.index R _ id _ _ => IdOk H R id

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

/-- The untyped memory value. -/
def MvT.erase : (T : Ty) → MvT T → Semantics.MVal
  | .prim p, v => .prim (PrimTy.erase (p := p) v)
  | .ref _, id => .ref id

/-- An identity written names an `R`. -/
def MvT.Ok (H : HTy) : (T : Ty) → MvT T → Prop
  | .prim _, _ => True
  | .ref R, id => IdOk H R id

/-- The slot value over the heap typing `H`. -/
def MvT.toMVal (H : HTy) : (T : Ty) → MvT T → Option (MVal H T)
  | .prim _, v => some v
  | .ref R, id => HRef.ofId? H R id

/-! ## What the sorts denote -/

/-- A typed sort's values, over the global part's heap typing `H`. -/
@[reducible] def SrtT.Den (C : Contract) (H : HTy) : SrtT → Type
  | .val p => p.Denote
  | .path T => SRef C T
  | .st => Storage C
  | .sv T => SVal T
  | .ident _ => Nat
  | .addr T => MAddrT T
  | .mem => Grown H (fun _ => Unit)
  | .mv T => MvT T

/-- The global part of a typed state: the state without its locals. -/
def State.glob {Γ : Ctx} (σ : State C Γ) : State C [] :=
  { storage := σ.storage, H := σ.H, heap := σ.heap, env := (), net := σ.net,
    selfBalance := σ.selfBalance, tx := σ.tx }

theorem State.glob_globE {Γ : Ctx} (σ : State C Γ) : σ.glob.globE = σ.globE := rfl

/-- The memory as it is: the heap grown by nothing. -/
def State.memT (g : State C []) : Grown g.H (fun _ => Unit) := ⟨List.prefix_refl _, g.heap, ()⟩

/-! ## Symbols -/

/-- Constants. -/
inductive OpT0 (C : Contract) : SrtT → Type where
  | lit {p : PrimTy} (v : p.Denote) : OpT0 C (.val p)
  | env (k : EnvKey) : OpT0 C (.val .uint)
  | root (r : Name) {T : Ty} (h : C.rootType r = some T) : OpT0 C (.path T)
  | storage : OpT0 C .st
  | memory : OpT0 C .mem
  /-- `mtSt`: every root of the contract at its default (`Storage.init`). -/
  | mtSt : OpT0 C .st

/-- Unary symbols. -/
inductive OpT1 (C : Contract) : SrtT → SrtT → Type where
  | unop (op : UnOp) {p : PrimTy} (h : op.accepts p = true) : OpT1 C (.val p) (.val (op.ret p))
  /-- `net(a)`: an `int`, where the ledger's entry is one. -/
  | net : OpT1 C (.val .uint) (.val .int)
  | delValue {p : PrimTy} : OpT1 C (.val p) (.val p)
  | field {s f : Name} {T : Ty} (h : C.fieldType s f = some T) :
      OpT1 C (.path (.ref (.struct s))) (.path T)
  | next {E : Ty} : OpT1 C (.path (.ref (.array E))) (.path E)
  | sval {p : PrimTy} : OpT1 C (.val p) (.sv (.prim p))
  | newArr {R : RefTy} (h : R.newArrOk = true) : OpT1 C (.val .uint) (.sv (.ref R))
  | alloc (R : RefTy) (h : (Ty.ref R).mapFree = true) : OpT1 C .mem (.ident R)
  | mfield {s f : Name} {T : Ty} (h : C.fieldType s f = some T) :
      OpT1 C (.ident (.struct s)) (.addr T)
  | addM (R : RefTy) (h : (Ty.ref R).mapFree = true) : OpT1 C .mem .mem
  | mval {p : PrimTy} : OpT1 C (.val p) (.mv (.prim p))
  | ref {R : RefTy} : OpT1 C (.ident R) (.mv (.ref R))
  | wt : OpT1 C .st (.val .bool)

/-- Binary symbols. -/
inductive OpT2 (C : Contract) : SrtT → SrtT → SrtT → Type where
  | binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true) :
      OpT2 C (.val p) (.val p) (.val (op.ret p))
  | find {p : PrimTy} : OpT2 C .st (.path (.prim p)) (.val p)
  | len {E : Ty} : OpT2 C .st (.path (.ref (.array E))) (.val .uint)
  | read {p : PrimTy} : OpT2 C .mem (.addr (.prim p)) (.val p)
  | mlen {E : Ty} : OpT2 C .mem (.ident (.array E)) (.val .uint)
  | at {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) :
      OpT2 C (.path (.ref R)) (.val k.keyTy) (.path V)
  | nextIn {E : Ty} : OpT2 C .st (.path (.ref (.array E))) (.path E)
  | delAt {T : Ty} : OpT2 C .st (.path T) .st
  | pushSlot {E : Ty} : OpT2 C .st (.path (.ref (.array E))) .st
  | pop {E : Ty} : OpT2 C .st (.path (.ref (.array E))) .st
  | shrink {E : Ty} : OpT2 C .st (.path (.ref (.array E))) .st
  | extend {E : Ty} : OpT2 C .st (.path (.ref (.array E))) .st
  | sfind {T : Ty} : OpT2 C .st (.path T) (.sv T)
  | copyMem {R : RefTy} : OpT2 C .mem (.ident R) (.sv (.ref R))
  | iread {R : RefTy} : OpT2 C .mem (.addr (.ref R)) (.ident R)
  | copy {R : RefTy} (h : (Ty.ref R).mapFree = true) : OpT2 C .mem (.sv (.ref R)) (.ident R)
  | mat {R : RefTy} {E : Ty} (a : ArrTy R E) : OpT2 C (.ident R) (.val .uint) (.addr E)
  | copySt {T : Ty} (h : T.mapFree = true) : OpT2 C .mem (.sv T) .mem

/-- Ternary symbols. -/
inductive OpT3 (C : Contract) : SrtT → SrtT → SrtT → SrtT → Type where
  | ite {p : PrimTy} : OpT3 C (.val .bool) (.val p) (.val p) (.val p)
  | save {T : Ty} : OpT3 C .st (.path T) (.sv T) .st
  | push {E : Ty} : OpT3 C .st (.path (.ref (.array E))) (.sv E) .st
  | atIn {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) :
      OpT3 C .st (.path (.ref R)) (.val k.keyTy) (.path V)
  | write {T : Ty} : OpT3 C .mem (.addr T) (.mv T) .mem

/-! ## Erasure to `Update.lean`'s symbols -/

def OpT0.erase {s : SrtT} : OpT0 C s → Op0 s.erase
  | .lit v => .lit (PrimTy.erase v)
  | .env k => .env k
  | .root r _ => .root r
  | .storage => .storage
  | .memory => .memory
  | .mtSt => .mtSt C.vars

def OpT1.erase {a s : SrtT} : OpT1 C a s → Op1 a.erase s.erase
  | .unop op (p := p) _ => .unop op p
  | .net => .net
  | .delValue => .delValue
  | @OpT1.field _ _ f _ _ => .field f
  | .next => .next
  | .sval => .sval
  | @OpT1.newArr _ R _ => .newArr R
  | .alloc R _ => .alloc R
  | @OpT1.mfield _ _ f _ _ => .mfield f
  | .addM R _ => .addM R
  | .mval => .mval
  | .ref => .ref
  | .wt => .wt C.vars

def OpT2.erase {a b s : SrtT} : OpT2 C a b s → Op2 a.erase b.erase s.erase
  | .binop op (p := p) _ => .binop op p
  | .find => .find
  | .len => .len
  | .read => .read
  | .mlen => .mlen
  | .at _ => .at
  | .nextIn => .nextIn
  | .delAt => .delAt
  | @OpT2.pushSlot _ E => .pushSlot E
  | .pop => .pop
  | .shrink => .shrink
  | @OpT2.extend _ E => .extend E
  | .sfind => .sfind
  | .copyMem => .copyMem
  | .iread => .iread
  | .copy _ => .copy
  | .mat _ => .mat
  | .copySt _ => .copySt

def OpT3.erase {a b c s : SrtT} : OpT3 C a b c s → Op3 a.erase b.erase c.erase s.erase
  | .ite => .ite
  | .save => .save
  | .push => .push
  | .atIn _ => .atIn
  | .write => .write


/-! ## Evaluation on the typed global part

An argument comes as an `Option`, as `Update.lean`'s comes as a `Res`: `&&`,
`||` and `c ? a : b` do not read the operand they do not need. -/

/-- A grown heap grown further. -/
def Grown.then {H : HTy} {α : HTy → Type} (m : Grown H (fun _ => Unit)) (n : Grown m.H' α) :
    Grown H (fun _ => Unit) :=
  ⟨m.ext.trans n.ext, n.heap, ()⟩

/-- The `storageWtB` test on a typed storage. -/
def Storage.wtT (st : Storage C) : Option PrimTy.bool.Denote :=
  if storageWtB C.vars st.erase then some (true : Bool) else none

/-- `p[p.length]` in `st`: the slot past the live elements. -/
def Storage.nextT {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) : Option (SRef C E) :=
  (st.find r).map fun v => r.index (.arr .dyn) ((SVal.view v : ArrView E).n : Int)

/-- `p[i]` with its index checked in `st`. -/
def Storage.atT {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C) (it : IndexTy R k V)
    (r : SRef C (.ref R)) (i : k.keyTy.Denote) : Option (SRef C V) := do
  st.checkIndex r it (PrimTy.key i)
  some (r.index it (PrimTy.key i))

/-- `OpT0.eval` by `match`, its compiled form. -/
def OpT0.evalM (g : State C []) {s : SrtT} : OpT0 C s → Option (s.Den C g.H)
  | .lit v => some v
  | .env k => some (g.envVal k)
  | .root r h => some (SRef.ofRoot r h)
  | .storage => some g.storage
  | .memory => some g.memT
  | .mtSt => some (Storage.init C)

/-- A constant on the typed global part. -/
@[implemented_by OpT0.evalM]
def OpT0.eval (g : State C []) {s : SrtT} (o : OpT0 C s) : Option (s.Den C g.H) :=
  @OpT0.casesOn C (fun s _ => Option (s.Den C g.H)) s o
    (fun {_} v => some v) (fun k => some (g.envVal k)) (fun r {_} h => some (SRef.ofRoot r h))
    (some g.storage) (some g.memT) (some (Storage.init C))

theorem OpT0.eval_eq_evalM (g : State C []) {s : SrtT} (o : OpT0 C s) : o.eval g = o.evalM g := by
  cases o <;> rfl

/-- `OpT1.eval` by `match`, its compiled form. -/
def OpT1.evalM (g : State C []) {a s : SrtT} :
    OpT1 C a s → Option (a.Den C g.H) → Option (s.Den C g.H)
  | .unop op _, x => x.bind op.evalT
  | .net, x => x.bind fun n => PrimTy.int.ofInt? ((lookupBy n.1 g.net).getD 0)
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

/-- A unary symbol on the typed global part. -/
@[implemented_by OpT1.evalM]
def OpT1.eval (g : State C []) {a s : SrtT} (o : OpT1 C a s) :
    Option (a.Den C g.H) → Option (s.Den C g.H) :=
  @OpT1.casesOn C (fun a s _ => Option (a.Den C g.H) → Option (s.Den C g.H)) a s o
    (fun op {_} _ x => x.bind op.evalT)
    (fun x => x.bind fun n => PrimTy.int.ofInt? ((lookupBy n.1 g.net).getD 0))
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

theorem OpT1.eval_eq_evalM (g : State C []) {a s : SrtT} (o : OpT1 C a s) :
    o.eval g = o.evalM g := by
  cases o <;> rfl

/-- `a ⊕ b`: `&&`/`||` decided by `a` alone (`BinOp.shortT`), else both. -/
def binopT (op : BinOp) {p : PrimTy} (a : p.Denote) (y : Option p.Denote) :
    Option (op.ret p).Denote :=
  match op.shortT a with
  | some r => some r
  | none => y.bind (op.evalT a)

/-- `read(m, a)`: the slot at `a` in `m`. -/
def Grown.readT {H : HTy} {T : Ty} (m : Grown H (fun _ => Unit)) (a : MAddrT T) :
    Option (MVal m.H' T) := do
  m.heap.readAddr (← a.resolve m.H')

/-- `write(m, a, v)`. -/
def Grown.writeT {H : HTy} {T : Ty} (m : Grown H (fun _ => Unit)) (a : MAddrT T) (v : MvT T) :
    Option (Grown H (fun _ => Unit)) := do
  let hp ← m.heap.writeAddr (← a.resolve m.H') (← MvT.toMVal m.H' T v)
  some ⟨m.ext, hp, ()⟩

/-- `OpT2.eval` by `match`, its compiled form. -/
def OpT2.evalM (g : State C []) {a b s : SrtT} :
    OpT2 C a b s → Option (a.Den C g.H) → Option (b.Den C g.H) → Option (s.Den C g.H)
  | .binop op _, x, y => x.bind fun a => binopT op a y
  | .find, x, y => do let v ← (← x).find (← y); some v.view
  | .len, x, y => do (← x).len (← y)
  | .read, x, y => do (← x).readT (← y)
  | @OpT2.mlen _ E, x, y => do
    let m ← x
    some (m.heap.lenU (← HRef.ofId? m.H' (.array E) (← y)))
  | .at it, x, y => do g.storage.atT it (← x) (← y)
  | .nextIn, x, y => do (← x).nextT (← y)
  | .delAt, x, y => do (← x).delete (← y)
  | .pushSlot, x, y => do (← x).push (← y) some
  | .pop, x, y => do (← x).pop false (← y)
  | .shrink, x, y => do (← x).pop true (← y)
  | .extend, x, y => do some ((← (← x).pushPlace (← y)).1)
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
  | .mat a, x, y => do some (.index (← x) a (← y).1)
  | .copySt h, x, y => do
    let m ← x
    some (m.then ((← y).copyStToM m.heap h))

/-- A binary symbol on the typed global part. -/
@[implemented_by OpT2.evalM]
def OpT2.eval (g : State C []) {a b s : SrtT} (o : OpT2 C a b s) :
    Option (a.Den C g.H) → Option (b.Den C g.H) → Option (s.Den C g.H) :=
  @OpT2.casesOn C
    (fun a b s _ => Option (a.Den C g.H) → Option (b.Den C g.H) → Option (s.Den C g.H)) a b s o
    (fun op {_} _ x y => x.bind fun a => binopT op a y)
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
    (fun {_} x y => do some ((← (← x).pushPlace (← y)).1))
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
    (fun {_} {_} a x y => do some (.index (← x) a (← y).1))
    (fun {_} h x y => do
      let m ← x
      some (m.then ((← y).copyStToM m.heap h)))

theorem OpT2.eval_eq_evalM (g : State C []) {a b s : SrtT} (o : OpT2 C a b s) :
    o.eval g = o.evalM g := by
  cases o <;> rfl

/-- `OpT3.eval` by `match`, its compiled form. -/
def OpT3.evalM (g : State C []) {a b c s : SrtT} :
    OpT3 C a b c s → Option (a.Den C g.H) → Option (b.Den C g.H) → Option (c.Den C g.H) →
      Option (s.Den C g.H)
  | .ite, x, y, z => x.bind fun c => cond c y z
  | .save, x, y, z => do (← x).write (← y) (← z)
  | .push, x, y, z => do (← x).push (← y) fun _ => z.map SVal.strip
  | .atIn it, x, y, z => do (← x).atT it (← y) (← z)
  | .write, x, y, z => do (← x).writeT (← y) (← z)

/-- A ternary symbol on the typed global part. -/
@[implemented_by OpT3.evalM]
def OpT3.eval (g : State C []) {a b c s : SrtT} (o : OpT3 C a b c s) :
    Option (a.Den C g.H) → Option (b.Den C g.H) → Option (c.Den C g.H) → Option (s.Den C g.H) :=
  @OpT3.casesOn C (fun a b c s _ => Option (a.Den C g.H) → Option (b.Den C g.H) →
      Option (c.Den C g.H) → Option (s.Den C g.H)) a b c s o
    (fun {_} x y z => x.bind fun c => cond c y z)
    (fun {_} x y z => do (← x).write (← y) (← z))
    (fun {_} x y z => do (← x).push (← y) fun _ => z.map SVal.strip)
    (fun {_} {_} {_} it x y z => do (← x).atT it (← y) (← z))
    (fun {_} x y z => do (← x).writeT (← y) (← z))

theorem OpT3.eval_eq_evalM (g : State C []) {a b c s : SrtT} (o : OpT3 C a b c s) :
    o.eval g = o.evalM g := by
  cases o <;> rfl


/-! ## The bridge: the typed evaluation erased -/

/-- A halt of the untyped evaluation, of any kind (`Calculus/RewritePast.lean`'s
`Srt.Halts`, which sits above this module; one goes at W9.8.5). -/
def Srt.IsHalt : (s : Srt) → s.Ev → Prop
  | .val, r => ∃ h, r = .error h
  | .path, r => ∃ h, r = .error h
  | .st, r => ∃ h, r = .error h
  | .sv, r => ∃ h, r = .error h
  | .ident, r => ∃ h, r = .error h
  | .addr, r => ∃ h, r = .error h
  | .mem, r => ∃ h, r = .error h
  | .mv, r => ∃ h, r = .error h

/-- A typed value as the untyped evaluation returns it, over the erased
global part: a storage or a memory is the global part with it. -/
def SrtT.okE (g : State C []) : (s : SrtT) → s.Den C g.H → s.erase.Ev
  | .val _, v => .ok (PrimTy.erase v)
  | .path _, r => .ok (SRef.erase r)
  | .st, w => .ok (Storage.into g.globE w)
  | .sv _, v => .ok (SVal.erase v)
  | .ident _, n => .ok n
  | .addr _, a => .ok (MAddrT.erase a)
  | .mem, m => .ok (Heap.into g.globE m.heap)
  | .mv T, v => .ok (MvT.erase T v)

/-- The untyped evaluation `r` agrees with the typed `x`: `x`'s value erased,
or some halt where `x` is `none`. -/
def SrtT.Agree (g : State C []) (s : SrtT) : Option (s.Den C g.H) → s.erase.Ev → Prop
  | some v, r => r = s.okE g v
  | none, r => s.erase.IsHalt r

/-- Where `OpT1.eval` is exact: `net(a)` an `int`. -/
def OpT1.Exact (g : State C []) {a s : SrtT} : OpT1 C a s → a.Den C g.H → Prop
  | .net, n => PrimTy.int.inRange ((lookupBy n.1 g.net).getD 0) = true
  | _, _ => True

/-- Where `OpT2.eval` is exact: an identity read has its type, a push room. -/
def OpT2.Exact (g : State C []) {a b s : SrtT} : OpT2 C a b s → a.Den C g.H → b.Den C g.H → Prop
  | .read, m, ad => MAddrT.Ok (Grown.H' m) ad
  | @OpT2.mlen _ E, m, id => IdOk (Grown.H' m) (.array E) id
  | @OpT2.copyMem _ R, m, id => IdOk (Grown.H' m) R id
  | .iread, m, ad => MAddrT.Ok (Grown.H' m) ad
  | .pushSlot, st, r => Storage.full st r = false
  | .extend, st, r => Storage.full st r = false
  | _, _, _ => True

/-- Where `OpT3.eval` is exact: a push has room, a write's identities their types. -/
def OpT3.Exact (g : State C []) {a b c s : SrtT} :
    OpT3 C a b c s → a.Den C g.H → b.Den C g.H → c.Den C g.H → Prop
  | .push, st, r, _ => Storage.full st r = false
  | @OpT3.write _ T, m, ad, v => MAddrT.Ok (Grown.H' m) ad ∧ MvT.Ok (Grown.H' m) T v
  | _, _, _, _ => True

/-- **The bridge for constants**: exact. -/
theorem OpT0.eval_agree (g : State C []) {s : SrtT} (o : OpT0 C s) :
    SrtT.Agree g s (o.eval g) (Op0.eval g.globE o.erase) := by
  rw [OpT0.eval_eq_evalM]
  cases o with
  | env k => cases k <;> rfl
  | mtSt =>
    simp only [OpT0.evalM, SrtT.Agree, SrtT.okE, Storage.into, Storage.init_erase,
      Contract.initStorage, OpT0.erase, Op0.eval]
    rfl
  | _ => rfl


section Bridge

variable (g : State C [])

theorem SrtT.agree_val {p : PrimTy} (x : Option p.Denote) :
    SrtT.Agree g (.val p) x (toRes PrimTy.erase x) := by
  cases x
  · exact ⟨.revert, rfl⟩
  · rfl

theorem SrtT.agree_path {T : Ty} (x : Option (SRef C T)) :
    SrtT.Agree g (.path T) x (toRes SRef.erase x) := by
  cases x
  · exact ⟨.revert, rfl⟩
  · rfl

theorem SrtT.agree_st (x : Option (Storage C)) :
    SrtT.Agree g .st x (toRes (Storage.into g.globE) x) := by
  cases x
  · exact ⟨.revert, rfl⟩
  · rfl

theorem SrtT.agree_sv {T : Ty} (x : Option (SVal T)) :
    SrtT.Agree g (.sv T) x (toRes SVal.erase x) := by
  cases x
  · exact ⟨.revert, rfl⟩
  · rfl

/-- **The bridge for unary symbols**: exact where `OpT1.Exact` holds. -/
theorem OpT1.eval_agree {a s : SrtT} (o : OpT1 C a s) {x : Option (a.Den C g.H)}
    {rx : a.erase.Ev} (hx : SrtT.Agree g a x rx) (he : ∀ v, x = some v → o.Exact g v) :
    SrtT.Agree g s (o.eval g x) (Op1.eval g.globE o.erase rx) := by
  rw [OpT1.eval_eq_evalM]
  cases x with
  | none =>
    cases o <;> (obtain ⟨h, rfl⟩ := hx; exact ⟨h, rfl⟩)
  | some v =>
    have he := he v rfl
    cases o with
    | unop op h =>
      subst hx
      show SrtT.Agree g (.val _) (op.evalT v)
        (do unopCheck op _ (← Semantics.applyUnOp op (PrimTy.erase v)) : Res Value)
      rw [UnOp.evalT_erase op h v]
      exact SrtT.agree_val g _
    | net =>
      subst hx
      simp only [OpT1.Exact] at he
      simp only [OpT1.evalM, Option.bind_some, PrimTy.ofInt?, PrimTy.ofValue?, dif_pos he]
      rfl
    | delValue => subst hx; cases ‹PrimTy› <;> rfl
    | field h =>
      subst hx
      show Except.ok _ = Except.ok (SRef.erase (v.field h))
      simp only [SRef.erase, SRef.field, SRef.append, Path.erase_append]
      rfl
    | next =>
      subst hx
      simp only [OpT1.evalM, OpT1.erase, Op1.eval, SrtT.okE, Option.bind_some, bind,
        Except.bind, SRef.erase, Storage.findStorage_erase (σ := g.globE) (st := g.storage) rfl,
        Storage.nextT]
      cases g.storage.find v with
      | none => exact ⟨.revert, rfl⟩
      | some w =>
        cases w with
        | array e sh h =>
          simp only [toRes, Option.map_some, SVal.erase_array, SVec.length_erase, SRef.index,
            SRef.append, SVal.view_array, SrtT.Agree, SrtT.okE, SRef.erase, Path.erase_append,
            Path.erase_index]
          rfl
    | sval =>
      subst hx
      show Except.ok _ = Except.ok (SVal.erase (SVal.prim v))
      rw [SVal.erase_prim]
      cases ‹PrimTy› <;> rfl
    | newArr h =>
      subst hx
      show Except.ok _ = Except.ok (SVal.erase (newArrT _ v h))
      rw [newArrT_erase]
    | alloc R h =>
      subst hx
      simp only [OpT1.evalM, OpT1.erase, Op1.eval, SrtT.okE, Option.map_some, bind, Except.bind,
        Heap.allocDefault_erase (σ := Heap.into g.globE v.heap) (hp := v.heap) rfl rfl R h]
      rfl
    | mfield h => subst hx; rfl
    | addM R h =>
      subst hx
      simp only [OpT1.evalM, OpT1.erase, Op1.eval, SrtT.okE, Option.map_some, bind, Except.bind,
        Heap.allocDefault_erase (σ := Heap.into g.globE v.heap) (hp := v.heap) rfl rfl R h]
      rfl
    | mval => subst hx; cases ‹PrimTy› <;> rfl
    | ref => subst hx; rfl
    | wt =>
      subst hx
      simp only [OpT1.evalM, OpT1.erase, Op1.eval, SrtT.okE, Option.bind_some, Storage.wtT,
        bind, Except.bind, Storage.into]
      split
      · rfl
      · exact ⟨.undef, rfl⟩


theorem binopT_some (op : BinOp) {p : PrimTy} (a b : p.Denote) :
    binopT op a (some b) = op.evalT a b := by
  unfold binopT
  cases op <;> cases p <;> (try cases a) <;> rfl

/-- `&&`/`||` with a halting right operand: the untyped one returns where the
typed one does. -/
theorem binopT_none_agree (op : BinOp) {p : PrimTy} (a : p.Denote) (h : Halt) :
    SrtT.Agree g (.val (op.ret p)) (binopT op a none)
      (evalBinop op p (PrimTy.erase a) (.error h)) := by
  unfold binopT
  cases op <;> cases p <;> (try cases a) <;> first | rfl | exact ⟨h, rfl⟩

/-- `p[i]` checked on the erasure. -/
theorem Storage.atT_erase {σ : Semantics.State} {st : Storage C} (hs : σ.storage = st.erase)
    {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (r : SRef C (.ref R))
    (i : k.keyTy.Denote) :
    (do σ.checkIndex r.root r.path.erase (PrimTy.key i)
        pure (r.root, r.path.erase ++ [Seg.at (PrimTy.key i)]) : Res (Name × List Seg)) =
      toRes SRef.erase (st.atT it r i) := by
  rw [Storage.checkIndex_erase hs r it]
  unfold Storage.atT
  cases st.checkIndex r it (PrimTy.key i) with
  | none => rfl
  | some u =>
    simp only [toRes, bind, Except.bind, Option.bind_some, SRef.erase,
      SRef.index, SRef.append, Path.erase_append, Path.erase_index]
    rfl

/-- A memory read on the erasure, its identity typed. -/
theorem Grown.readT_erase {H : HTy} {T : Ty} (m : Grown H (fun _ => Unit)) {σ : Semantics.State}
    (hh : σ.heap = m.heap.erase) (ad : MAddrT T) (hok : ad.Ok m.H') :
    readAddr σ ad.erase = toRes (MVal.erase T) (m.readT ad) := by
  cases ad with
  | field id h =>
    simp only [MAddrT.Ok] at hok
    simp only [Grown.readT, MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_of_ok hok,
      Option.map_some, Option.bind_eq_bind, Option.bind_some, Heap.readAddr, readAddr,
      MAddrT.erase]
    exact Heap.readField_erase hh ⟨id, hok⟩ h
  | index id a i =>
    simp only [MAddrT.Ok] at hok
    simp only [Grown.readT, MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_of_ok hok,
      Option.map_some, Option.bind_eq_bind, Option.bind_some, Heap.readAddr, readAddr,
      MAddrT.erase]
    exact Heap.readIndex_erase hh ⟨id, hok⟩ a i

/-- The binary symbols on two values, exact. -/
theorem OpT2.agree_some {a b s : SrtT} (o : OpT2 C a b s) (u : a.Den C g.H) (v : b.Den C g.H)
    (he : o.Exact g u v) :
    SrtT.Agree g s (o.evalM g (some u) (some v)) (Op2.eval g.globE o.erase (a.okE g u) (b.okE g v)) := by
  cases o with
  | binop op h =>
    simp only [OpT2.evalM, Option.bind_some, binopT_some]
    show SrtT.Agree g (.val _) _ (evalBinop op _ (PrimTy.erase u) (.ok (PrimTy.erase v)))
    rw [BinOp.evalT_erase op h u v]
    exact SrtT.agree_val g _
  | find =>
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, SRef.erase,
      Storage.findStorage_erase (σ := Storage.into g.globE u) (st := u) rfl]
    cases u.find v with
    | none => exact ⟨.revert, rfl⟩
    | some w =>
      cases w
      simp only [toRes, Option.bind_some, SVal.erase_prim, SrtT.Agree, SrtT.okE, SVal.view_prim]
      cases ‹PrimTy› <;> rfl
  | len =>
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, SRef.erase,
      Storage.arrayLen_erase (σ := Storage.into g.globE u) (st := u) rfl]
    exact SrtT.agree_val g _
  | read =>
    simp only [OpT2.Exact] at he
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, Grown.readT_erase u (σ := Heap.into g.globE u.heap) rfl v he]
    cases u.readT v with
    | none => exact ⟨.revert, rfl⟩
    | some w => cases ‹PrimTy› <;> rfl
  | mlen =>
    simp only [OpT2.Exact] at he
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, HRef.ofId?_of_ok he]
    have hl := Heap.memArrayLen_erase (σ := Heap.into g.globE u.heap) (hp := u.heap) rfl
      (⟨v, he⟩ : HRef u.H' _) .dyn
    rw [hl]
    rfl
  | «at» it =>
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, SRef.erase, PrimTy.asInt_erase_keyTy]
    have ha := Storage.atT_erase (σ := g.globE) (st := g.storage) rfl it u v
    simp only [bind, Except.bind] at ha
    rw [ha]
    exact SrtT.agree_path g _
  | nextIn =>
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, SRef.erase,
      Storage.findStorage_erase (σ := Storage.into g.globE u) (st := u) rfl, Storage.nextT]
    cases u.find v with
    | none => exact ⟨.revert, rfl⟩
    | some w =>
      cases w with
      | array e sh h =>
        simp only [toRes, Option.map_some, SVal.erase_array, SVec.length_erase, SRef.index,
          SRef.append, SVal.view_array, SrtT.Agree, SrtT.okE, SRef.erase, Path.erase_append,
          Path.erase_index]
        rfl
  | delAt =>
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, SRef.erase]
    have hd := Storage.delete_erase (σ := Storage.into g.globE u) (st := u) rfl v
    simp only [bind, Except.bind] at hd
    rw [hd]
    exact SrtT.agree_st g _
  | pushSlot =>
    simp only [OpT2.Exact] at he
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, SRef.erase]
    rw [Storage.pushAt_erase (σ := Storage.into g.globE u) (st := u) rfl v pure some
      (fun _ => rfl) (.inl he)]
    exact SrtT.agree_st g _
  | pop =>
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, SRef.erase,
      Storage.popAt_erase (σ := Storage.into g.globE u) (st := u) rfl]
    exact SrtT.agree_st g _
  | shrink =>
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, SRef.erase,
      Storage.popAt_erase (σ := Storage.into g.globE u) (st := u) rfl]
    exact SrtT.agree_st g _
  | extend =>
    simp only [OpT2.Exact] at he
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, SRef.erase,
      Storage.pushPlaceAt_erase (σ := Storage.into g.globE u) (st := u) rfl v he]
    cases u.pushPlace v with
    | none => exact ⟨.revert, rfl⟩
    | some w => rfl
  | sfind =>
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, SRef.erase,
      Storage.findStorage_erase (σ := Storage.into g.globE u) (st := u) rfl]
    exact SrtT.agree_sv g _
  | copyMem =>
    simp only [OpT2.Exact] at he
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, HRef.ofId?_of_ok he]
    rw [show Semantics.MVal.ref v = MVal.erase (.ref _) (⟨v, he⟩ : HRef u.H' _) from rfl,
      MVal.copyMem_erase (σ := Heap.into g.globE u.heap) (hp := u.heap) rfl]
    rfl
  | iread =>
    simp only [OpT2.Exact] at he
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind, Grown.readT_erase u (σ := Heap.into g.globE u.heap) rfl v he]
    cases u.readT v with
    | none => exact ⟨.revert, rfl⟩
    | some w => rfl
  | copy h =>
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind,
      SVal.copyStToM_erase v h u.heap (Heap.into g.globE u.heap) rfl rfl]
    rfl
  | mat a => rfl
  | copySt h =>
    simp only [OpT2.evalM, OpT2.erase, Op2.eval, SrtT.okE, Option.bind_some,
      bind, Except.bind,
      SVal.copyStToM_erase v h u.heap (Heap.into g.globE u.heap) rfl rfl]
    rfl

/-- **The bridge for binary symbols**: exact where `OpT2.Exact` holds. -/
theorem OpT2.eval_agree {a b s : SrtT} (o : OpT2 C a b s) {x : Option (a.Den C g.H)}
    {y : Option (b.Den C g.H)} {rx : a.erase.Ev} {ry : b.erase.Ev}
    (hx : SrtT.Agree g a x rx) (hy : SrtT.Agree g b y ry)
    (he : ∀ u v, x = some u → y = some v → o.Exact g u v) :
    SrtT.Agree g s (o.eval g x y) (Op2.eval g.globE o.erase rx ry) := by
  rw [OpT2.eval_eq_evalM]
  cases o <;> cases x <;> cases y <;>
    first
    | (obtain ⟨h, rfl⟩ := hx; obtain ⟨h', rfl⟩ := hy; first | exact ⟨h, rfl⟩ | exact ⟨h', rfl⟩)
    | (obtain ⟨h, rfl⟩ := hx; subst hy; exact ⟨h, rfl⟩)
    | (subst hx; obtain ⟨h', rfl⟩ := hy; exact ⟨h', rfl⟩)
    | (subst hx; subst hy; exact OpT2.agree_some g _ _ _ (he _ _ rfl rfl))
    | (subst hx; obtain ⟨h', rfl⟩ := hy; exact binopT_none_agree g _ _ h')


/-- A push whose element halts halts. -/
theorem pushAt_error (σ : Semantics.State) (E : Ty) (r : Name) (segs : List Seg) (h : Halt) :
    ∃ h', pushAt σ E r segs (fun _ => .error h) = .error h' := by
  unfold pushAt
  cases σ.findStorage r segs with
  | error h' => exact ⟨h', rfl⟩
  | ok d =>
    cases d with
    | array elems sh fx => exact ⟨h, rfl⟩
    | _ => exact ⟨.undef, rfl⟩

theorem MvT.toMVal_ok {H : HTy} : (T : Ty) → (v : MvT T) → MvT.Ok H T v →
    ∃ v' : MVal H T, MvT.toMVal H T v = some v' ∧ MvT.erase T v = MVal.erase T v'
  | .prim _, v, _ => ⟨v, rfl, rfl⟩
  | .ref _, v, hv => ⟨⟨v, hv⟩, HRef.ofId?_of_ok hv, rfl⟩

/-- A memory write on the erasure, its identities typed. -/
theorem Grown.writeT_erase {H : HTy} {T : Ty} (m : Grown H (fun _ => Unit)) (σ : Semantics.State)
    (ad : MAddrT T) (v : MvT T) (hok : ad.Ok m.H') (hv : MvT.Ok m.H' T v) :
    writeAddr (Heap.into σ m.heap) (MvT.erase T v) ad.erase =
      toRes (fun m' : Grown H (fun _ => Unit) => Heap.into σ m'.heap) (m.writeT ad v) := by
  obtain ⟨v', htv, hev⟩ := MvT.toMVal_ok T v hv
  rw [hev]
  cases ad with
  | field id h =>
    simp only [MAddrT.Ok] at hok
    simp only [Grown.writeT, MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_of_ok hok,
      Option.map_some, Option.bind_eq_bind, Option.bind_some, htv, Heap.writeAddr, writeAddr,
      MAddrT.erase]
    rw [Heap.memWriteField_erase (σ := Heap.into σ m.heap) rfl ⟨id, hok⟩ h v']
    rfl
  | index id a i =>
    simp only [MAddrT.Ok] at hok
    simp only [Grown.writeT, MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_of_ok hok,
      Option.map_some, Option.bind_eq_bind, Option.bind_some, htv, Heap.writeAddr, writeAddr,
      MAddrT.erase]
    rw [Heap.memWriteIndex_erase (σ := Heap.into σ m.heap) rfl ⟨id, hok⟩ a i v']
    cases m.heap.setIndex ⟨id, hok⟩ a i v' <;> rfl

/-- The ternary symbols on three values, exact. -/
theorem OpT3.agree_some {a b c s : SrtT} (o : OpT3 C a b c s) (u : a.Den C g.H)
    (v : b.Den C g.H) (w : c.Den C g.H) (he : o.Exact g u v w) :
    SrtT.Agree g s (o.evalM g (some u) (some v) (some w))
      (Op3.eval g.globE o.erase (a.okE g u) (b.okE g v) (c.okE g w)) := by
  cases o with
  | ite => cases u <;> rfl
  | save =>
    simp only [OpT3.evalM, OpT3.erase, Op3.eval, SrtT.okE, Option.bind_some, bind, Except.bind,
      SRef.erase, Storage.writeStorage_erase (σ := Storage.into g.globE u) (st := u) rfl]
    exact SrtT.agree_st g _
  | push =>
    simp only [OpT3.Exact] at he
    simp only [OpT3.evalM, OpT3.erase, Op3.eval, SrtT.okE, Option.bind_some, bind, Except.bind,
      SRef.erase, Option.map_some]
    rw [pushAt_const _ _ ‹Ty›,
      Storage.pushAt_erase (σ := Storage.into g.globE u) (st := u) rfl v _ (fun _ => some w.strip)
        (fun _ => by simp only [toRes, SVal.strip_erase]; rfl) (.inl he)]
    exact SrtT.agree_st g _
  | atIn it =>
    simp only [OpT3.evalM, OpT3.erase, Op3.eval, SrtT.okE, Option.bind_some, bind, Except.bind,
      SRef.erase, PrimTy.asInt_erase_keyTy]
    have ha := Storage.atT_erase (σ := Storage.into g.globE u) (st := u) rfl it v w
    simp only [bind, Except.bind] at ha
    rw [ha]
    exact SrtT.agree_path g _
  | write =>
    simp only [OpT3.Exact] at he
    simp only [OpT3.evalM, OpT3.erase, Op3.eval, SrtT.okE, Option.bind_some, bind, Except.bind,
      Grown.writeT_erase u g.globE v w he.1 he.2]
    cases u.writeT v w with
    | none => exact ⟨.revert, rfl⟩
    | some m' => rfl

theorem OpT3.ite_agree {p : PrimTy} (cv : Bool) {y z : Option p.Denote} {ry rz : Res Value}
    (hy : SrtT.Agree g (.val p) y ry) (hz : SrtT.Agree g (.val p) z rz) :
    SrtT.Agree g (.val p) (OpT3.evalM g .ite (some cv) y z)
      (Op3.eval g.globE .ite (.ok (.bool cv)) ry rz) := by
  cases cv
  · exact hz
  · exact hy

theorem Storage.push_none {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) :
    st.push r (fun _ => none) = none := by
  unfold Storage.push
  cases st.find r <;> rfl

theorem OpT3.push_none_agree {E : Ty} (u : Storage C) (v : SRef C (.ref (.array E))) (h : Halt) :
    SrtT.Agree g .st (OpT3.evalM g .push (some u) (some v) none)
      (Op3.eval g.globE .push (SrtT.okE g .st u) (SrtT.okE g (.path _) v) (.error h)) := by
  simp only [OpT3.evalM, Option.bind_eq_bind, Option.bind_some, Option.map_none,
    Storage.push_none]
  exact pushAt_error _ _ _ _ h

/-- **The bridge for ternary symbols**: exact where `OpT3.Exact` holds. -/
theorem OpT3.eval_agree {a b c s : SrtT} (o : OpT3 C a b c s) {x : Option (a.Den C g.H)}
    {y : Option (b.Den C g.H)} {z : Option (c.Den C g.H)} {rx : a.erase.Ev} {ry : b.erase.Ev}
    {rz : c.erase.Ev} (hx : SrtT.Agree g a x rx) (hy : SrtT.Agree g b y ry)
    (hz : SrtT.Agree g c z rz)
    (he : ∀ u v w, x = some u → y = some v → z = some w → o.Exact g u v w) :
    SrtT.Agree g s (o.eval g x y z) (Op3.eval g.globE o.erase rx ry rz) := by
  rw [OpT3.eval_eq_evalM]
  cases o <;> cases x <;> cases y <;> cases z <;>
    first
    | (subst hx; subst hy; subst hz; exact OpT3.agree_some g _ _ _ _ (he _ _ _ rfl rfl rfl))
    | (subst hx; exact OpT3.ite_agree g _ hy hz)
    | (subst hx; subst hy; obtain ⟨h₃, rfl⟩ := hz; exact OpT3.push_none_agree g _ _ h₃)
    | ((try obtain ⟨h₁, rfl⟩ := hx); (try obtain ⟨h₂, rfl⟩ := hy); (try obtain ⟨h₃, rfl⟩ := hz)
       (try subst hx); (try subst hy); (try subst hz)
       first | exact ⟨h₁, rfl⟩ | exact ⟨h₂, rfl⟩ | exact ⟨h₃, rfl⟩)

end Bridge


/-! ## The Theory's abstraction

`Fml.eq` reads the Theory (`Theory.StValue`, KeY's total model), so a typed
value is read there through its erasure (decision of the W9.8.0 spike): the
Theory stays untyped. -/

/-- A typed storage value as a Theory term (`Semantics.SVal.abs` of its
erasure). -/
def SVal.absT {T : Ty} (v : SVal T) : Theory.StValue := Semantics.SVal.abs v.erase

/-- A typed storage as one Theory struct node (`State.abs`). -/
def Storage.absT (st : Storage C) : Theory.Struct := Semantics.SVal.abs.fields st.erase

theorem Storage.abs_into (σ : Semantics.State) (st : Storage C) :
    (Storage.into σ st).abs = st.absT := rfl

theorem State.abs_globE {Γ : Ctx} (σ : State C Γ) : σ.globE.abs = σ.storage.absT := rfl

/-! ## The laws, typed

solkey's `findOnSave` and `findOnSaveDifferent` (`TermTaclet.findOnSave`,
`TermTaclet.findOnSaveFrame`) on the typed storage, where the write lands
(the Theory's `find_copyTo_same` and `find_copyTo_frame`, `Theory/Copy.lean`,
need no premise: KeY's model is total).  A typed `save` is the program's
write (`Storage.write`: a word stored, a struct or an array laid over what is
there), which is a `Storage.save` at the same reference. -/

theorem SFields.get_set_same {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (x : SFields fs) →
    (h : lookupBy f fs = some T) → (y : SVal T) → (x.set h y).get h = y
  | [], _, .nil, h, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons v rest, h, y => by
    rw [SFields.set_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true, SFields.get_cons]
    · simp only [e, dite_false, SFields.get_cons]
      exact SFields.get_set_same rest _ y

theorem SFields.get_set_ne {f g : Name} : {fs : List (Name × Ty)} → {T U : Ty} → (x : SFields fs) →
    (h : lookupBy f fs = some T) → (hg : lookupBy g fs = some U) → f ≠ g → (y : SVal T) →
    (x.set h y).get hg = x.get hg
  | [], _, _, .nil, h, _, _, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, U, .cons v rest, h, hg, hfg, y => by
    rw [SFields.set_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      have eg : ¬ g = f' := fun h' => hfg (e.trans h'.symm)
      simp only [e, dite_true, SFields.get_cons, eg, dite_false]
    · simp only [e, dite_false, SFields.get_cons]
      by_cases eg : g = f'
      · simp only [eg, dite_true]
      · simp only [eg, dite_false]
        exact SFields.get_set_ne rest _ _ hfg y

theorem SVal.findM_saveM : {T U : Ty} → (x : SVal T) → (p : Path T U) → (v : SVal U) →
    {x' : SVal T} → x.saveM p v = some x' → x'.findM p = some v
  | _, _, x, .nil, v, x', h => by
    cases x <;> (simp only [SVal.saveM, Option.some.injEq] at h; subst h; cases v <;> rfl)
  | _, _, .struct fs, .field hf p, v, x', h => by
    simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨y, hy, rfl⟩ := h
    simp only [SVal.findM, SFields.get_set_same]
    exact SVal.findM_saveM _ p v hy
  | _, _, .array e sh hn, .at i p, v, x', h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i hi
      split at h
      · rename_i x hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨y, hy, rfl⟩ := h
        have hl : i.toNat < (e.toList ++ sh.toList).length := (List.getElem?_eq_some_iff.mp hx).1
        simp only [SVal.findM, hi, if_true, SVec.toList_ofList, SList.toList_ofList,
          List.take_append_drop, List.getElem?_set_self hl]
        exact SVal.findM_saveM _ p v hy
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  | _, _, .fixed e, .atF i p, v, x', h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i hi
      split at h
      · rename_i x hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨y, hy, rfl⟩ := h
        have hl : i.toNat < e.toList.length := (List.getElem?_eq_some_iff.mp hx).1
        simp only [SVal.findM, hi, if_true, SVec.toList_set, List.getElem?_set_self hl]
        exact SVal.findM_saveM _ p v hy
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  | _, _, .map m d, .key k p, v, x', h => by
    simp only [SVal.saveM] at h
    split at h <;>
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨y, hy, rfl⟩ := h
      simp only [SVal.findM, SMap.toList_ofList, SemanticsProperties.lookupBy_setBy_self]
      exact SVal.findM_saveM _ p v hy

/-- A save that lands reads back (`findOnSave` below a root). -/
theorem SVal.find_save_same {T U : Ty} (x : SVal T) (p : Path T U) (v : SVal U)
    {x' : SVal T} (h : x.save p v = some x') : x'.find p = some v := by
  rw [SVal.save_eq_saveM] at h
  rw [SVal.find_eq_findM]
  exact SVal.findM_saveM x p v h

/-- Two paths from one value that part: at two members, two slots or two
keys, somewhere along them (solkey's `p ≠ q` of `findOnSaveDifferent`,
across the types the two paths reach). -/
inductive Path.Diverges : {T U W : Ty} → Path T U → Path T W → Prop
  | field {s f f' : Name} {T T' U W : Ty} (h : lookupBy f (structDef s) = some T)
      (h' : lookupBy f' (structDef s) = some T') (p : Path T U) (q : Path T' W) (hne : f ≠ f') :
      Diverges (.field h p) (.field h' q)
  | fieldIn {s f : Name} {T U W : Ty} (h : lookupBy f (structDef s) = some T) {p : Path T U}
      {q : Path T W} : Diverges p q → Diverges (.field h p) (.field h q)
  | at {E U W : Ty} {i j : Int} (p : Path E U) (q : Path E W) (hne : i ≠ j) :
      Diverges (.at i p) (.at j q)
  | atIn {E U W : Ty} (i : Int) {p : Path E U} {q : Path E W} :
      Diverges p q → Diverges (.at i p) (.at i q)
  | atF {E U W : Ty} {n : Nat} {i j : Int} (p : Path E U) (q : Path E W) (hne : i ≠ j) :
      Diverges (.atF (n := n) i p) (.atF j q)
  | atFIn {E U W : Ty} {n : Nat} (i : Int) {p : Path E U} {q : Path E W} :
      Diverges p q → Diverges (.atF (n := n) i p) (.atF i q)
  | key {K V U W : Ty} {k k' : Int} (p : Path V U) (q : Path V W) (hne : k ≠ k') :
      Diverges (.key (K := K) k p) (.key k' q)
  | keyIn {K V U W : Ty} (k : Int) {p : Path V U} {q : Path V W} :
      Diverges p q → Diverges (.key (K := K) k p) (.key k q)

theorem SVal.findM_saveM_diverges {T U W : Ty} {p : Path T U} {q : Path T W}
    (hd : Path.Diverges p q) : (x : SVal T) → (v : SVal U) → {x' : SVal T} →
    x.saveM p v = some x' → x'.findM q = x.findM q := by
  induction hd with
  | field h h' p q hne =>
    intro x v x' hs
    cases x with
    | struct fs =>
      simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hs
      obtain ⟨y, _, rfl⟩ := hs
      simp only [SVal.findM, SFields.get_set_ne fs h h' hne]
  | fieldIn h _ ih =>
    intro x v x' hs
    cases x with
    | struct fs =>
      simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hs
      obtain ⟨y, hy, rfl⟩ := hs
      simp only [SVal.findM, SFields.get_set_same]
      exact ih _ v hy
  | @«at» E U W i j p q hne =>
    intro x v x' hs
    cases x with
    | array e sh hn =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i hi
        split at hs
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
          obtain ⟨y, _, rfl⟩ := hs
          simp only [SVal.findM, SVec.toList_ofList, SList.toList_ofList, List.take_append_drop]
          by_cases hj : 0 ≤ j
          · have hn' : i.toNat ≠ j.toNat := by omega
            simp only [hj, if_true, List.getElem?_set_ne hn']
          · simp only [hj, if_false]
        · simp only [reduceCtorEq] at hs
      · simp only [reduceCtorEq] at hs
  | atIn i _ ih =>
    intro x v x' hs
    cases x with
    | array e sh hn =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i hi
        split at hs
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
          obtain ⟨y, hy, rfl⟩ := hs
          have hl : i.toNat < (e.toList ++ sh.toList).length :=
            (List.getElem?_eq_some_iff.mp hx).1
          simp only [SVal.findM, hi, if_true, SVec.toList_ofList, SList.toList_ofList,
            List.take_append_drop, List.getElem?_set_self hl, hx]
          exact ih _ v hy
        · simp only [reduceCtorEq] at hs
      · simp only [reduceCtorEq] at hs
  | @atF E U W n i j p q hne =>
    intro x v x' hs
    cases x with
    | fixed e =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i hi
        split at hs
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
          obtain ⟨y, _, rfl⟩ := hs
          simp only [SVal.findM, SVec.toList_set]
          by_cases hj : 0 ≤ j
          · have hn' : i.toNat ≠ j.toNat := by omega
            simp only [hj, if_true, List.getElem?_set_ne hn']
          · simp only [hj, if_false]
        · simp only [reduceCtorEq] at hs
      · simp only [reduceCtorEq] at hs
  | atFIn i _ ih =>
    intro x v x' hs
    cases x with
    | fixed e =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i hi
        split at hs
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
          obtain ⟨y, hy, rfl⟩ := hs
          have hl : i.toNat < e.toList.length := (List.getElem?_eq_some_iff.mp hx).1
          simp only [SVal.findM, hi, if_true, SVec.toList_set, List.getElem?_set_self hl, hx]
          exact ih _ v hy
        · simp only [reduceCtorEq] at hs
      · simp only [reduceCtorEq] at hs
  | @key K V U W k k' p q hne =>
    intro x v x' hs
    cases x with
    | map m d =>
      simp only [SVal.saveM] at hs
      split at hs <;>
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, _, rfl⟩ := hs
        simp only [SVal.findM, SMap.toList_ofList,
          SemanticsProperties.lookupBy_setBy_ne (Ne.symm hne)]
  | keyIn k _ ih =>
    intro x v x' hs
    cases x with
    | map m d =>
      simp only [SVal.saveM] at hs
      split at hs
      · rename_i x0 hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, hy, rfl⟩ := hs
        simp only [SVal.findM, SMap.toList_ofList, SemanticsProperties.lookupBy_setBy_self, hx]
        exact ih _ v hy
      · rename_i hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
        obtain ⟨y, hy, rfl⟩ := hs
        simp only [SVal.findM, SMap.toList_ofList, SemanticsProperties.lookupBy_setBy_self, hx]
        exact ih _ v hy

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
(solkey's `findOnSave`; Theory `find_copyTo_same`). -/
theorem findOnSave {p : PrimTy} (st : Storage C) (r : SRef C (.prim p)) (v : p.Denote)
    {st' : Storage C} (h : st.write r (.prim v) = some st') : st'.find r = some (.prim v) := by
  obtain ⟨x', hs, rfl⟩ := save_some (show st.save r (.prim v) = some st' from h)
  simp only [Storage.find, SFields.get_set_same]
  exact SVal.find_save_same _ _ _ hs

/-- **`findOnSaveFrame`** across roots, typed: a write leaves another state
variable as it was (solkey's `findOnSaveDifferent`; Theory
`find_copyTo_frame`). -/
theorem findOnSaveFrameRoot {U W : Ty} (st : Storage C) (r : SRef C U) (q : SRef C W)
    (hne : r.root ≠ q.root) (v : SVal U) {st' : Storage C} (h : st.write r v = some st') :
    st'.find q = st.find q := by
  obtain ⟨w, hw⟩ := write_some h
  obtain ⟨x', _, rfl⟩ := save_some hw
  simp only [Storage.find, SFields.get_set_ne _ r.hroot q.hroot hne]

/-- **`findOnSaveFrame`** below one root, typed: a write leaves a path that
parts from it as it was (solkey's `findOnSaveDifferent`, `p ≠ q` as
`Path.Diverges`; Theory `find_copyTo_frame`). -/
theorem findOnSaveFrame {T U W : Ty} (st : Storage C) (r : Name) (hr : C.rootType r = some T)
    {p : Path T U} {q : Path T W} (hd : Path.Diverges p q) (v : SVal U) {st' : Storage C}
    (h : st.write ⟨r, hr, p⟩ v = some st') :
    st'.find ⟨r, hr, q⟩ = st.find ⟨r, hr, q⟩ := by
  obtain ⟨w, hw⟩ := write_some h
  obtain ⟨x', hs, rfl⟩ := save_some hw
  simp only [Storage.find, SFields.get_set_same]
  rw [SVal.save_eq_saveM] at hs
  rw [SVal.find_eq_findM, SVal.find_eq_findM]
  exact SVal.findM_saveM_diverges hd _ w hs

end Storage

end Solidity
