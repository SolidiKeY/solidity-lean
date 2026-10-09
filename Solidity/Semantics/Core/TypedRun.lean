import Solidity.Semantics.Core.TypedState
import Solidity.Semantics.Core.Ops

/-!
# The typed run

`Semantics/Core.lean`'s interpreter on typed values (`docs/intrinsic.md`,
"M4 lane", wiring items 3 and 4): a state is a `TState` (typed storage, a
heap and its typing, the locals typed over it), a storage path resolves to
an `SRef` (an index by `SRef.atKey`, a mapping's key as it is hashed), a
memory path to a heap reference read through `Heap.field`/`Heap.index`, and
an operator is `BinOp.evalT`/`UnOp.evalT`.  A run ends in a state or halts
with `THalt`: `revert`, `panic`, `diverge` or `exhausted`; there is no
`stuck`.

A dynamic array holds fewer than `2^256` elements (`SVal.array`, `MObj`), so
a length is a `uint` (`Storage.len`, `Heap.lenU`).  A push onto `2^256 - 1`
elements exhausts the resources: the run halts with `exhausted`
(`Storage.full`, decision 15), which both modalities accept, as KeY, which
models no gas, reads every run that runs out of it; the untyped run, which
has no bound, may go on (`docs/solc-alignment.md`, "Array lengths").

The heap only grows, and a call sets its caller's locals aside while the body
runs, so each step returns its state with the extension of the heap typing
(`Out`): the caller's locals are weakened along it when the call returns.

As in `Semantics/Core.lean`, each statement's step is one function
(`TRun.*`) given its sub-programs' runs, `Stmt.trun`/`Prog.trun` are the
recursor over them (`Stmt.trunR`, Gate G0 conditions 1 and 2) with a
`match` twin for the compiler (`Stmt.trunC`, linked by `Stmt.trunR_eq`).
-/

namespace Solidity

/-- A literal at its type: a number in the type's range (a `bool` has no
numeric literal). -/
def PrimTy.ofLit : (p : PrimTy) → (n : Int) → p.inRange n = true → p.Denote
  | .uint, n, h => (⟨n, h⟩ : {n : Int // PrimTy.uint.inRange n = true})
  | .int, n, h => (⟨n, h⟩ : {n : Int // PrimTy.int.inRange n = true})
  | .bool, _, h => absurd h (by simp only [PrimTy.inRange, Bool.false_eq_true, not_false_eq_true])

theorem RefTy.mapFree_of_newArrOk {R : RefTy} (h : R.newArrOk = true) :
    (Ty.ref R).mapFree = true := by
  cases R <;> simp only [RefTy.newArrOk, Bool.and_eq_true, Bool.false_eq_true] at h
  exact h.1

namespace Core

open Semantics (Value Seg Halt Res lookupBy setBy ExtKey ExtResult structDef)

variable {C : Contract}

/-! ## Results -/

/-- How a typed run halts: no `stuck`.  `exhausted` is a push past the
bound (`Storage.full`): resource exhaustion, which both modalities accept
(`Modality.onTHalt`, decision 15). -/
inductive THalt where
  | revert
  | panic
  | diverge
  | exhausted
  deriving Repr, DecidableEq, Inhabited

abbrev TRes (α : Type) := Except THalt α

def THalt.erase : THalt → Halt
  | .revert => .revert
  | .panic => .panic
  | .diverge => .diverge
  | .exhausted => .diverge

/-- A typed result as an untyped one. -/
def TRes.erase {α β : Type} (f : α → β) : TRes α → Res β
  | .ok a => .ok (f a)
  | .error h => .error h.erase

/-- A typed operation's `none` reverts. -/
def TRes.ofOpt {α : Type} : Option α → TRes α
  | some a => .ok a
  | none => .error .revert

/-- A `bool` value as the Boolean it is. -/
@[reducible] def boolT (b : PrimTy.bool.Denote) : Bool := b

/-! ## States -/

/-- A state with the heap typing it started from below its own: what a step
leaves. -/
structure Out (C : Contract) (H : HTy) (Γ : Ctx) where
  st : TState C Γ
  ext : H <+: st.H

/-- A state over a grown heap, its extension, and a value over its typing. -/
structure Grew (C : Contract) (Γ : Ctx) (H : HTy) (α : HTy → Type) where
  st : TState C Γ
  ext : H <+: st.H
  val : α st.H

namespace TEnv

variable {H : HTy}

/-- The locals `ρ` on top of `Γ`'s. -/
def append {Γ : Ctx} : (ρ : Ctx) → TEnv C H ρ → TEnv C H Γ → TEnv C H (ρ ++ Γ)
  | [], _, e => e
  | _ :: ρ, r, e => (r.1, TEnv.append ρ r.2 e)

/-- The top `ρ` of the locals. -/
def take {Γ : Ctx} : (ρ : Ctx) → TEnv C H (ρ ++ Γ) → TEnv C H ρ
  | [], _ => ()
  | _ :: ρ, e => (e.1, TEnv.take ρ e.2)

end TEnv

namespace TState

variable {Γ : Ctx}

/-- The locals replaced, in another context. -/
def withEnv {Δ : Ctx} (σ : TState C Γ) (e : TEnv C σ.H Δ) : TState C Δ :=
  { storage := σ.storage, H := σ.H, heap := σ.heap, env := e, net := σ.net,
    selfBalance := σ.selfBalance, tx := σ.tx }

/-- The objects replaced, at the same typing. -/
def withHeap (σ : TState C Γ) (hp : Heap σ.H) : TState C Γ := { σ with heap := hp }

/-- A grown heap adopted, with its extension (`adopt`). -/
def grow {α : HTy → Type} (σ : TState C Γ) (g : Grown σ.H α) : Grew C Γ σ.H α :=
  ⟨(σ.adopt g).1, g.ext, g.val⟩

/-- A fresh default object (`allocDefault`), with the extension. -/
def allocDefaultG (σ : TState C Γ) (R : RefTy) (h : (Ty.ref R).mapFree = true) :
    Grew C Γ σ.H (MVal · (.ref R)) :=
  σ.grow (σ.heap.allocDefault R h)

/-- A storage value copied into fresh objects (`copyStToM`), with the
extension. -/
def copyStToMG {T : Ty} (σ : TState C Γ) (v : SVal T) (h : T.mapFree = true) :
    Grew C Γ σ.H (MVal · T) :=
  σ.grow (v.copyStToM σ.heap h)

/-- A value of the environment. -/
def envVal (σ : TState C Γ) : EnvKey → PrimTy.uint.Denote
  | .msgSender => σ.tx.msgSender
  | .msgValue => σ.tx.msgValue
  | .timestamp => σ.tx.timestamp
  | .selfBalance => σ.selfBalance
  | .selfAddress => σ.tx.selfAddress

/-- `amt` paid to `addr` on the ledger (`State.pay`): nothing booked for the
contract itself. -/
def pay (σ : TState C Γ) (addr amt : Int) : TState C Γ :=
  { σ with net := if addr = σ.tx.selfAddress.1 then σ.net
      else setBy addr ((lookupBy addr σ.net).getD 0 - amt) σ.net }

/-- A state with no locals and no memory, over a storage. -/
def ofStorage (st : Storage C) : TState C [] :=
  { storage := st, H := [], heap := Heap.empty, env := () }

end TState

/-! ## Memory addresses -/

/-- A memory location, resolved: a struct's member, or an element. -/
inductive MAddr (H : HTy) : Ty → Type where
  | field {s f : Name} {T : Ty} (r : HRef H (.struct s)) (h : lookupBy f (structDef s) = some T) :
      MAddr H T
  | index {R : RefTy} {E : Ty} (r : HRef H R) (a : ArrTy R E) (i : Int) : MAddr H E

/-- An address over a grown heap. -/
def MAddr.wk {H H' : HTy} (e : H <+: H') {T : Ty} : MAddr H T → MAddr H' T
  | .field r h => .field (r.wk e) h
  | .index r a i => .index (r.wk e) a i

namespace Heap

variable {H : HTy}

/-- The slot at an address (`readAddr`): an element out of bounds reverts. -/
def readAddr (hp : Heap H) {T : Ty} : MAddr H T → Option (MVal H T)
  | .field r h => some (hp.field r h)
  | .index r a i => hp.index r a i

/-- The slot at an address written (`writeAddr`). -/
def writeAddr (hp : Heap H) {T : Ty} : MAddr H T → MVal H T → Option (Heap H)
  | .field r h, v => some (hp.setField r h v)
  | .index r a i, v => hp.setIndex r a i v

end Heap

/-! ## Operators -/

/-- `a && b` and `a || b` decided by `a` alone: the right operand is not
evaluated (`evalBinop`'s first arms). -/
def _root_.Solidity.BinOp.shortT : (op : BinOp) → {p : PrimTy} → p.Denote → Option (op.ret p).Denote
  | .and, .bool, x => if boolT x then none else some (false : Bool)
  | .or, .bool, x => if boolT x then some (true : Bool) else none
  | _, _, _ => none

/-- `a ⊕= b` at a numeric type: the operator on the integers, then the range
check (`opStore`). -/
def compoundT (op : BinOp) (p : PrimTy) (x y : Int) : Option p.Denote :=
  (BinOp.arithInt op x y).bind p.ofInt?

/-- `x++`/`x--` at a numeric type (`bumpStore`). -/
def bumpT (op : IncDec) (p : PrimTy) (x : Int) : Option p.Denote :=
  p.ofInt? (if op.isIncrement then x + 1 else x - 1)

/-- `n` elements, `n` a `uint`: below the bound. -/
theorem newArr_lt {E : Ty} (n : PrimTy.uint.Denote) (v : SVal E) :
    (List.replicate n.1.toNat v).length < 2 ^ 256 := by
  have h := n.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  rw [List.length_replicate]
  omega

/-- What `new R(n)` allocates, as the storage value it is a copy of
(`newArrVal`): `n` default elements. -/
def newArrT : (R : RefTy) → PrimTy.uint.Denote → R.newArrOk = true → SVal (.ref R)
  | .array E, n, _ => .array (SVec.ofList (List.replicate n.1.toNat (SVal.dflt E))) .nil
      (newArr_lt n _)
  | .struct _, _, h | .fixed .., _, h | .mapping .., _, h =>
    absurd h (by simp only [RefTy.newArrOk, Bool.false_eq_true, not_false_eq_true])

/-! ## Expressions -/

section Eval

variable {Γ : Ctx}

/-- The value a simple value denotes. -/
def Simple.evalT (σ : TState C Γ) : {p : PrimTy} → Simple C Γ p → p.Denote
  | p, .lit n h => PrimTy.ofLit p n h
  | _, .bool b => (b : Bool)
  | _, .local i => TEnv.get i σ.env
  | _, .env k hp => hp ▸ σ.envVal k

mutual

/-- The storage reference a path denotes: an unset alias reverts. -/
def SPath.resolveT (σ : TState C Γ) : {T : Ty} → SPath C Γ T → TRes (SRef C T)
  | _, .alias i =>
    match (TEnv.get i σ.env : Option (SRef C _)) with
    | some r => .ok r
    | none => .error .revert
  | _, .loc l => l.resolveT σ

def Loc.resolveT (σ : TState C Γ) : {T : Ty} → Loc C Γ T → TRes (SRef C T)
  | _, .root r h => .ok (SRef.ofRoot r h)
  | _, .field b _ h => do
    let r ← b.resolveT σ
    pure (r.field h)
  | _, .index it b i => do
    let r ← b.resolveT σ
    let k ← i.evalT σ
    TRes.ofOpt (σ.storage.checkIndex r it (PrimTy.key k))
    pure (r.atKey it k)

/-- The slot a memory path holds: an unset memory local reverts, as an
unset alias does (decision 17'). -/
def MPath.mvalT (σ : TState C Γ) : {T : Ty} → MPath C Γ T → TRes (MVal σ.H T)
  | _, .var i _ =>
    match (TEnv.get i σ.env : Option (HRef σ.H _)) with
    | some r => .ok r
    | none => .error .revert
  | _, .loc l => do TRes.ofOpt (σ.heap.readAddr (← l.addrT σ))

/-- The address of a memory location: the object, then the index. -/
def MLoc.addrT (σ : TState C Γ) : {T : Ty} → MLoc C Γ T → TRes (MAddr σ.H T)
  | _, .field b _ h => do
    let r ← b.mvalT σ
    pure (.field r h)
  | _, .index a b i => do
    let r ← b.mvalT σ
    let k ← i.evalT σ
    pure (.index r a k.1)

/-- The value a value expression denotes. -/
def Val.evalT (σ : TState C Γ) : {p : PrimTy} → Val C Γ p → TRes p.Denote
  | _, .simple s => .ok (s.evalT σ)
  | _, .read l => do
    let r ← l.resolveT σ
    let v ← TRes.ofOpt (σ.storage.find r)
    pure v.view
  | _, .binop op _ hq a b => do
    let x ← a.evalT σ
    match op.shortT x with
    | some y => pure (hq ▸ y)
    | none => do
      let y ← b.evalT σ
      hq ▸ TRes.ofOpt (op.evalT x y)
  | _, .unop op _ hq a => do
    let x ← a.evalT σ
    hq ▸ TRes.ofOpt (op.evalT x)
  | _, .ternary c a b => do
    let v ← c.evalT σ
    if boolT v then a.evalT σ else b.evalT σ
  | _, .readMem l => do TRes.ofOpt (σ.heap.readAddr (← l.addrT σ))
  | _, .len b hp => do
    let r ← b.resolveT σ
    let n ← TRes.ofOpt (σ.storage.len r)
    pure (hp ▸ n)
  | _, .mlen b hp => do
    let r ← b.mvalT σ
    pure (hp ▸ σ.heap.lenU r)

end

/-- The storage value a source stores. -/
def Src.valueT (σ : TState C Γ) {T : Ty} : Src C Γ T → TRes (SVal T)
  | .val v => do pure (.prim (← v.evalT σ))
  | .copy p _ => do
    let r ← p.resolveT σ
    TRes.ofOpt (σ.storage.find r)

/-- The slot a memory source writes. -/
def MSrc.mvalT (σ : TState C Γ) {T : Ty} : MSrc C Γ T → TRes (MVal σ.H T)
  | .val v => v.evalT σ
  | .ref p => p.mvalT σ

/-- The storage a storage alias's right-hand side leaves (a push grows an
array), and the reference it names. -/
def ARhs.evalT (σ : TState C Γ) {R : RefTy} : ARhs C Γ R → TRes (Storage C × SRef C (.ref R))
  | .path p => do pure (σ.storage, ← p.resolveT σ)
  | .push b _ => do
    let r ← b.resolveT σ
    if σ.storage.full r then .error .exhausted else
    let (st, n) ← TRes.ofOpt (σ.storage.pushPlace r)
    pure (st, r.index (.arr .dyn) n)

/-- The object a memory right-hand side names, and the state its allocation
leaves. -/
def MRhs.evalT (σ : TState C Γ) {R : RefTy} : MRhs C Γ R → TRes (Grew C Γ σ.H (HRef · R))
  | .alias p => do
    let r ← p.mvalT σ
    pure ⟨σ, List.prefix_refl _, r⟩
  | .copy p hm => do
    let r ← p.resolveT σ
    let sv ← TRes.ofOpt (σ.storage.find r)
    let g := σ.copyStToMG sv hm
    pure ⟨g.st, g.ext, g.val⟩
  | .newArr n h =>
    let g := σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)
    .ok ⟨g.st, g.ext, g.val⟩

/-- `a ⊕= v` at a storage reference: read, apply, check, write back. -/
def opStoreT (σ : TState C Γ) (op : BinOp) {p : PrimTy} (r : SRef C (.prim p)) (v : p.Denote) :
    TRes (Out C σ.H Γ) := do
  let old ← TRes.ofOpt (σ.storage.find r)
  let new ← TRes.ofOpt (compoundT op p (PrimTy.key (SVal.view old)) (PrimTy.key v))
  let st ← TRes.ofOpt (σ.storage.save r (.prim new))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

/-- `a ⊕= v` at a memory address. -/
def opMemT (σ : TState C Γ) (op : BinOp) {p : PrimTy} (a : MAddr σ.H (.prim p)) (v : p.Denote) :
    TRes (Out C σ.H Γ) := do
  let old ← TRes.ofOpt (σ.heap.readAddr a)
  let new ← TRes.ofOpt (compoundT op p (PrimTy.key (p := p) old) (PrimTy.key v))
  let hp ← TRes.ofOpt (σ.heap.writeAddr a new)
  pure ⟨σ.withHeap hp, List.prefix_refl _⟩

/-- A compound assignment's write of `v` into its target. -/
def OpLoc.storeT (σ : TState C Γ) (op : BinOp) : {p : PrimTy} → OpLoc C Γ p → p.Denote →
    TRes (Out C σ.H Γ)
  | p, .local i, v => do
    let new ← TRes.ofOpt (compoundT op p (PrimTy.key (TEnv.get i σ.env)) (PrimTy.key v))
    pure ⟨σ.setLocal i new, List.prefix_refl _⟩
  | _, .root r h, v => opStoreT σ op (SRef.ofRoot r h) v
  | _, .field b f h, v => do opStoreT σ op (← (Loc.field b f h).resolveT σ) v
  | _, .index it b i, v => do opStoreT σ op (← (Loc.index it b (.simple i)).resolveT σ) v
  | _, .mfield b f h, v => do opMemT σ op (← (MLoc.field b f h).addrT σ) v
  | _, .mindex a b i, v => do opMemT σ op (← (MLoc.index a b (.simple i)).addrT σ) v

/-- `x++` at a storage reference: the state, and the value. -/
def bumpStoreT (σ : TState C Γ) (op : IncDec) {p : PrimTy} (r : SRef C (.prim p)) :
    TRes (Out C σ.H Γ × p.Denote) := do
  let old ← TRes.ofOpt (σ.storage.find r)
  let new ← TRes.ofOpt (bumpT op p (PrimTy.key (SVal.view old)))
  let st ← TRes.ofOpt (σ.storage.save r (.prim new))
  pure (⟨σ.withStorage st, List.prefix_refl _⟩, if op.isPre then new else SVal.view old)

/-- `x++` at a memory address. -/
def bumpMemT (σ : TState C Γ) (op : IncDec) {p : PrimTy} (a : MAddr σ.H (.prim p)) :
    TRes (Out C σ.H Γ × p.Denote) := do
  let old ← TRes.ofOpt (σ.heap.readAddr a)
  let new ← TRes.ofOpt (bumpT op p (PrimTy.key (p := p) old))
  let hp ← TRes.ofOpt (σ.heap.writeAddr a new)
  pure (⟨σ.withHeap hp, List.prefix_refl _⟩, if op.isPre then new else old)

/-- `l++`: the state it leaves, and its value. -/
def OpLoc.bumpT (σ : TState C Γ) (op : IncDec) : {p : PrimTy} → OpLoc C Γ p →
    TRes (Out C σ.H Γ × p.Denote)
  | p, .local i => do
    let old : p.Denote := TEnv.get i σ.env
    let new ← TRes.ofOpt (Solidity.Core.bumpT op p (PrimTy.key old))
    pure (⟨σ.setLocal i new, List.prefix_refl _⟩, if op.isPre then new else old)
  | _, .root r h => bumpStoreT σ op (SRef.ofRoot r h)
  | _, .field b f h => do bumpStoreT σ op (← (Loc.field b f h).resolveT σ)
  | _, .index it b i => do bumpStoreT σ op (← (Loc.index it b (.simple i)).resolveT σ)
  | _, .mfield b f h => do bumpMemT σ op (← (MLoc.field b f h).addrT σ)
  | _, .mindex a b i => do bumpMemT σ op (← (MLoc.index a b (.simple i)).addrT σ)

/-- `pv = a.send(v);` with both evaluated (`sendAt`): a payment refused books
nothing and sets `pv` to `false`. -/
def sendT (σ : TState C Γ) (pv : Idx Γ (.val .bool)) (addr amt : Int) : Out C σ.H Γ :=
  match lookupBy (sendKey addr amt) σ.tx.ext with
  | none | some (.ok _) => ⟨(σ.pay addr amt).setLocal pv (true : Bool), List.prefix_refl _⟩
  | some _ => ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩

/-- The call as it is made: its receiver and arguments, untyped. -/
def ExtCall.keyT (σ : TState C Γ) (c : ExtCall C Γ) : ExtKey :=
  ⟨(c.addr.evalT σ).1, c.fn, c.args.map fun a => PrimTy.erase (a.2.evalT σ)⟩

/-- A call's arguments, each read in the caller's state, in order. -/
def Args.evalT (σ : TState C Γ) : {ps : Ctx} → Args C Γ ps → TRes (TEnv C σ.H ps)
  | _, as => Args.casesOn (motive := fun ps _ => TRes (TEnv C σ.H ps)) as (pure ())
      (fun as _ _ e => do
        let r ← Args.evalT σ as
        let v ← e.evalT σ
        pure (v, r))
  termination_by structural _ as => as

end Eval

/-- The return variables at their defaults. -/
def Binders.defaultsT {H : HTy} : {ρ : Ctx} → Binders ρ → TEnv C H ρ
  | _, bs => Binders.casesOn (motive := fun ρ _ => TEnv C H ρ) bs ()
      (fun bs p _ => (PrimTy.dflt p, Binders.defaultsT bs))
  termination_by structural _ bs => bs

/-- The locals an external call's data binds, read back at their types, and
the data left: too short, or a word not of its local's type, reverts. -/
def Binders.decodeT {H : HTy} : {ρ : Ctx} → Binders ρ → List Value → TRes (TEnv C H ρ × List Value)
  | _, bs => Binders.casesOn
      (motive := fun ρ _ => List Value → TRes (TEnv C H ρ × List Value)) bs
      (fun vs => pure ((), vs))
      (fun bs p _ vs => do
        let (e, rest) ← Binders.decodeT bs vs
        match rest with
        | v :: rest =>
          match PrimTy.ofValue? p v with
          | some x => pure ((x, e), rest)
          | none => .error .revert
        | [] => .error .revert)
  termination_by structural _ bs => bs

/-- The `Panic` code bound, if the clause names it. -/
def CodeBinder.decodeT {H : HTy} {κ : Ctx} (code : CodeBinder κ) (c : Value) :
    TRes (TEnv C H κ) :=
  CodeBinder.casesOn (motive := fun κ _ => TRes (TEnv C H κ)) code (pure ())
    (fun _ => match PrimTy.ofValue? .uint c with
      | Option.some x => pure (x, ())
      | Option.none => .error .revert)

/-- Entering a call: its return variables at their defaults on the frame's
parameters (a memory return a fresh default object). -/
def CallRet.enterT {Γ : Ctx} {rs Γ' : Ctx} (ret : CallRet Γ rs Γ') {ps : Ctx}
    (τ : TState C ps) : Out C τ.H (rs ++ ps) :=
  CallRet.casesOn (motive := fun rs _ _ => Out C τ.H (rs ++ ps)) ret
    ⟨τ, List.prefix_refl _⟩
    (fun p _ _ => ⟨τ.push (t := .val p) (PrimTy.dflt p), List.prefix_refl _⟩)
    (fun {rs} bs => ⟨τ.withEnv (TEnv.append rs (Binders.defaultsT bs) τ.env), List.prefix_refl _⟩)
    (fun R _ _ hm =>
      let g := τ.allocDefaultG R hm
      ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩)

/-- Leaving a call: the caller's locals `e`, with what the call leaves them. -/
def CallRet.leaveT {H : HTy} {Γ : Ctx} (e : TEnv C H Γ) {rs Γ' : Ctx} (ret : CallRet Γ rs Γ') :
    TEnv C H rs → TEnv C H Γ' :=
  CallRet.casesOn (motive := fun rs Γ' _ => TEnv C H rs → TEnv C H Γ') ret
    (fun _ => e)
    (fun _ _ res r => match res with
      | .some i => TEnv.set i r.1 e
      | .none => e)
    (fun {rs} _ r => TEnv.append rs r e)
    (fun _ _ _ _ r => (r.1, e))

/-! ## Loops

`Semantics/Core.lean`'s `Loop` on typed results: the condition is a
`Bool`. -/

namespace TLoop

variable {α : Type}

def step (body : α → TRes α) (c : α → TRes Bool) (σ : α) : α ⊕ TRes α :=
  match c σ with
  | .error h => .inr (.error h)
  | .ok false => .inr (.ok σ)
  | .ok true =>
    match body σ with
    | .error h => .inr (.error h)
    | .ok τ => .inl τ

def iterN (body : α → TRes α) (c : α → TRes Bool) : Nat → α → α ⊕ TRes α
  | 0, σ => .inl σ
  | n + 1, σ =>
    match step body c σ with
    | .inl τ => iterN body c n τ
    | .inr r => .inr r

partial def runImpl [Inhabited α] (body : α → TRes α) (c : α → TRes Bool) (σ : α) : TRes α :=
  match step body c σ with
  | .inl τ => runImpl body c τ
  | .inr r => r

/-- The compiled loop, for a state type with no `Inhabited` instance. -/
def runImpl' (body : α → TRes α) (c : α → TRes Bool) (σ : α) : TRes α :=
  @runImpl α ⟨σ⟩ body c σ

open Classical in
/-- The loop's outcome, or `diverge` when no iteration is done. -/
@[implemented_by runImpl']
noncomputable def run (body : α → TRes α) (c : α → TRes Bool) (σ : α) : TRes α :=
  if h : ∃ r n, iterN body c n σ = .inr r then Classical.choose h else .error .diverge

theorem iterN_done_le {body : α → TRes α} {c : α → TRes Bool} {n m : Nat} {σ : α} {r : TRes α}
    (hnm : n ≤ m) (h : iterN body c n σ = .inr r) : iterN body c m σ = .inr r := by
  induction n generalizing σ m with
  | zero => simp only [iterN, reduceCtorEq] at h
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [iterN] at h ⊢
    cases hs : step body c σ with
    | inl τ => rw [hs] at h; exact ih (by omega) h
    | inr r' => rw [hs] at h; exact h

theorem iterN_done_unique {body : α → TRes α} {c : α → TRes Bool} {n m : Nat} {σ : α}
    {r r' : TRes α} (h : iterN body c n σ = .inr r) (h' : iterN body c m σ = .inr r') :
    r = r' := by
  rcases Nat.le_total n m with hnm | hmn
  · rw [iterN_done_le hnm h] at h'
    exact Sum.inr.inj h'
  · rw [iterN_done_le hmn h'] at h
    exact (Sum.inr.inj h).symm

/-- A loop done at `n` ends as it is done there. -/
theorem run_of_iterN {body : α → TRes α} {c : α → TRes Bool} {n : Nat} {σ : α} {r : TRes α}
    (h : iterN body c n σ = .inr r) : run body c σ = r := by
  have hex : ∃ r n, iterN body c n σ = .inr r := ⟨r, n, h⟩
  simp only [run, hex, dite_true]
  obtain ⟨n', h'⟩ := Classical.choose_spec hex
  exact iterN_done_unique h' h

/-- A loop no iteration finishes diverges. -/
theorem run_of_not_done {body : α → TRes α} {c : α → TRes Bool} {σ : α}
    (h : ∀ n, ∃ τ, iterN body c n σ = .inl τ) : run body c σ = .error .diverge := by
  have hex : ¬∃ r n, iterN body c n σ = .inr r := fun ⟨r, n, hn⟩ => by
    obtain ⟨τ, hτ⟩ := h n
    rw [hn] at hτ
    cases hτ
  simp only [run, hex, dite_false]

end TLoop

/-! ## Statements -/

/-- A step: from a state, the state it leaves over a grown heap. -/
abbrev TStep (C : Contract) (Γ Γ' : Ctx) : Type := (σ : TState C Γ) → TRes (Out C σ.H Γ')

namespace TRun

variable {Γ : Ctx}

def assign {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : TStep C Γ Γ := fun σ => do
  let sv ← r.valueT σ
  let ref ← l.resolveT σ
  let st ← TRes.ofOpt (σ.storage.write ref sv)
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

def rebind {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) : TStep C Γ Γ := fun σ => do
  let (st, ref) ← r.evalT σ
  pure ⟨(σ.withStorage st).setLocal i (some ref), List.prefix_refl _⟩

def assignLocal {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) : TStep C Γ Γ := fun σ => do
  pure ⟨σ.setLocal i (← r.evalT σ), List.prefix_refl _⟩

def declLocal (p : PrimTy) (init : Option (Val C Γ p)) : TStep C Γ (.val p :: Γ) := fun σ => do
  let v ← match init with
    | none => pure (PrimTy.dflt p)
    | some e => e.evalT σ
  pure ⟨σ.push (t := .val p) v, List.prefix_refl _⟩

def declStorage (R : RefTy) (init : Option (ARhs C Γ R)) : TStep C Γ (.alias R :: Γ) := fun σ =>
  match init with
  | none => pure ⟨σ.push (t := .alias R) none, List.prefix_refl _⟩
  | some r => do
    let (st, ref) ← r.evalT σ
    pure ⟨(σ.withStorage st).push (t := .alias R) (some ref), List.prefix_refl _⟩

def opAssign {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (r : Val C Γ p) : TStep C Γ Γ :=
  fun σ => do l.storeT σ op (← r.evalT σ)

def incDec {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) : TStep C Γ Γ := fun σ => do
  pure (← l.bumpT σ op).1

def assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (l : OpLoc C Γ p) :
    TStep C Γ Γ := fun σ => do
  let (o, v) ← l.bumpT σ op
  pure ⟨o.st.setLocal i v, o.ext⟩

def push {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) : TStep C Γ Γ := fun σ => do
  let ref ← b.resolveT σ
  let x ← match v with
    | none => pure none
    | some r => do pure (some (← r.valueT σ).strip)
  if σ.storage.full ref then .error .exhausted else
  let st ← TRes.ofOpt (σ.storage.push ref fun slot => some (x.getD slot))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

def pop {E : Ty} (b : SPath C Γ (.array E)) : TStep C Γ Γ := fun σ => do
  let ref ← b.resolveT σ
  let st ← TRes.ofOpt (σ.storage.pop E.isMapping ref)
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

def transfer (r a : Val C Γ .uint) : TStep C Γ Γ := fun σ => do
  let addr ← r.evalT σ
  let amt ← a.evalT σ
  pure ⟨σ.pay addr.1 amt.1, List.prefix_refl _⟩

def send (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) : TStep C Γ Γ := fun σ => do
  let addr ← r.evalT σ
  let amt ← a.evalT σ
  pure (sendT σ pv addr.1 amt.1)

def declMem (R : RefTy) (init : Option (MRhs C Γ R)) (hm : (Ty.ref R).mapFree = true) :
    TStep C Γ (.mem R :: Γ) := fun σ =>
  match init with
  | none =>
    let g := σ.allocDefaultG R hm
    pure ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩
  | some r => do
    let g ← r.evalT σ
    pure ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩

def rebindMem {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) : TStep C Γ Γ := fun σ => do
  let g ← r.evalT σ
  pure ⟨g.st.setLocal i (some g.val), g.ext⟩

def assignFromMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) : TStep C Γ Γ :=
  fun σ => do
    let m ← p.mvalT σ
    let ref ← l.resolveT σ
    let st ← TRes.ofOpt (σ.storage.write ref (MVal.copyMToSt σ.heap m))
    pure ⟨σ.withStorage st, List.prefix_refl _⟩

def assignMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : TStep C Γ Γ := fun σ => do
  let mv ← r.mvalT σ
  let a ← l.addrT σ
  let hp ← TRes.ofOpt (σ.heap.writeAddr a mv)
  pure ⟨σ.withHeap hp, List.prefix_refl _⟩

def delete {T : Ty} (l : Loc C Γ T) : TStep C Γ Γ := fun σ => do
  let ref ← l.resolveT σ
  let st ← TRes.ofOpt (σ.storage.delete ref)
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

/-- `delete` at a memory address (`memClear`): a word to its default, a
reference to a fresh default object. -/
def clearT (σ : TState C Γ) : {T : Ty} → MAddr σ.H T → T.mapFree = true → TRes (Out C σ.H Γ)
  | .prim p, a, _ => do
    let hp ← TRes.ofOpt (σ.heap.writeAddr a (PrimTy.dflt p))
    pure ⟨σ.withHeap hp, List.prefix_refl _⟩
  | .ref R, a, hm =>
    let g := σ.allocDefaultG R hm
    match g.st.heap.writeAddr (a.wk g.ext) g.val with
    | some hp => .ok ⟨g.st.withHeap hp, g.ext⟩
    | none => .error .revert

def deleteMem {T : Ty} (p : MPath C Γ T) : TStep C Γ Γ := fun σ =>
  match p with
  | .var i hm =>
    let g := σ.allocDefaultG _ hm
    pure ⟨g.st.setLocal i (some g.val), g.ext⟩
  | .loc l => do clearT σ (← l.addrT σ) l.mapFree

def assignNew {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint) (h : R.newArrOk = true) :
    TStep C Γ Γ := fun σ =>
  let g := σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)
  match l with
  | .store l => do
    let ref ← l.resolveT g.st
    let st ← TRes.ofOpt (g.st.storage.write ref (MVal.copyMToSt g.st.heap g.val))
    pure ⟨g.st.withStorage st, g.ext⟩
  | .mem l => do
    let a ← l.addrT g.st
    let hp ← TRes.ofOpt (g.st.heap.writeAddr a g.val)
    pure ⟨g.st.withHeap hp, g.ext⟩

/-- `if`: the branch the condition picks, its locals popped. -/
def ite {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) (thn : TStep C Γ Γ₁)
    (h₂ : Ext Γ Γ₂) (els : TStep C Γ Γ₂) : TStep C Γ Γ := fun σ => do
  let v ← c.evalT σ
  if boolT v then (thn σ).map fun o => ⟨o.st.drop h₁, o.ext⟩
  else (els σ).map fun o => ⟨o.st.drop h₂, o.ext⟩

def require (c : Val C Γ .bool) : TStep C Γ Γ := fun σ => do
  let v ← c.evalT σ
  if boolT v then pure ⟨σ, List.prefix_refl _⟩ else .error .revert

def assert (c : Val C Γ .bool) : TStep C Γ Γ := fun σ => do
  let v ← c.evalT σ
  if boolT v then pure ⟨σ, List.prefix_refl _⟩ else .error .panic

/-- A call: the arguments read, the frame entered, the body run in it, and
the caller's locals, weakened along the heap the body grew, with what the call
leaves them. -/
def call {Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf) : TStep C Γ Γ' := fun σ => do
  let a ← args.evalT σ
  let o₁ := ret.enterT (σ.withEnv a)
  let o ← body o₁.st
  let e : σ.H <+: o.st.H := o₁.ext.trans o.ext
  pure ⟨o.st.withEnv
    (ret.leaveT (TEnv.wk e Γ σ.env) (TEnv.take rs (TEnv.drop hb o.st.env))), e⟩

/-- `try`: the clause the transaction's outcome picks, its locals popped. -/
def tryCall {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : TStep C (ρ ++ Γ) Γ₁)
    (h₂ : Ext Γ Γ₂) (err : TStep C Γ Γ₂) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : TStep C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : TStep C Γ Γ₄) : TStep C Γ Γ := fun σ =>
  match lookupBy (call.keyT σ) σ.tx.ext with
  | none => .error .revert
  | some (.ok vs) => do
    let (r, _) ← rets.decodeT (H := σ.H) vs
    (ok (σ.withEnv (TEnv.append ρ r σ.env))).map fun o =>
      ⟨o.st.drop ((Ext.append Γ ρ).trans h₁), o.ext⟩
  | some .error => (err σ).map fun o => ⟨o.st.drop h₂, o.ext⟩
  | some (.panic c) => do
    let r ← code.decodeT (H := σ.H) c
    (pnc (σ.withEnv (TEnv.append κ r σ.env))).map fun o =>
      ⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩
  | some .other => (other σ).map fun o => ⟨o.st.drop h₄, o.ext⟩

/-- `while`: the body's locals popped every iteration, the heap's extension
carried from the loop's start. -/
def loop {Γ₁ : Ctx} (c : Val C Γ .bool) (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁) : TStep C Γ Γ :=
  fun σ => TLoop.run
    (fun o : Out C σ.H Γ => (body o.st).map fun o' => ⟨o'.st.drop h, o.ext.trans o'.ext⟩)
    (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩

/-- A block: its locals popped. -/
def block {Γ₁ : Ctx} (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁) : TStep C Γ Γ := fun σ =>
  (body σ).map fun o => ⟨o.st.drop h, o.ext⟩

/-- A sequence: the first statement, then the rest. -/
def seq {Γ₁ Γ₂ : Ctx} (s : TStep C Γ Γ₁) (P : TStep C Γ₁ Γ₂) : TStep C Γ Γ₂ := fun σ =>
  match s σ with
  | .ok o => (P o.st).map fun o' => ⟨o'.st, o.ext.trans o'.ext⟩
  | .error e => .error e

/-- The empty sequence. -/
def nil : TStep C Γ Γ := fun σ => .ok ⟨σ, List.prefix_refl _⟩

end TRun

/-! ## Running a program -/

mutual

/-- The compiled typed run of a statement. -/
def Stmt.trunC : {Γ Γ' : Ctx} → Stmt C Γ Γ' → TStep C Γ Γ'
  | _, _, .assign l r => TRun.assign l r
  | _, _, .rebind i r => TRun.rebind i r
  | _, _, .assignLocal i r => TRun.assignLocal i r
  | _, _, .declLocal p _ init => TRun.declLocal p init
  | _, _, .declStorage R _ init => TRun.declStorage R init
  | _, _, .opAssign op _ _ l r => TRun.opAssign op l r
  | _, _, .incDec op _ l => TRun.incDec op l
  | _, _, .assignIncDec i op _ l _ => TRun.assignIncDec i op l
  | _, _, .push b v _ => TRun.push b v
  | _, _, .pop b => TRun.pop b
  | _, _, .transfer r a => TRun.transfer r a
  | _, _, .send pv r a => TRun.send pv r a
  | _, _, .declMem R _ init _ hm => TRun.declMem R init hm
  | _, _, .rebindMem i r => TRun.rebindMem i r
  | _, _, .assignFromMem l p => TRun.assignFromMem l p
  | _, _, .assignMem l r => TRun.assignMem l r
  | _, _, .delete l => TRun.delete l
  | _, _, .deleteMem p _ => TRun.deleteMem p
  | _, _, .assignNew l n h => TRun.assignNew l n h
  | _, _, .ite c thn els => TRun.ite c thn.ext (Prog.trunC thn) els.ext (Prog.trunC els)
  | _, _, .require c => TRun.require c
  | _, _, .assert c => TRun.assert c
  | _, _, .revert => fun _ => .error .revert
  | _, _, .call _ args ret body => TRun.call args ret body.ext (Prog.trunC body)
  | _, _, .tryCall call rets ok err code pnc other =>
    TRun.tryCall call rets ok.ext (Prog.trunC ok) err.ext (Prog.trunC err) code pnc.ext
      (Prog.trunC pnc) other.ext (Prog.trunC other)
  | _, _, .loop _ c body => TRun.loop c body.ext (Prog.trunC body)
  | _, _, .block body => TRun.block body.ext (Prog.trunC body)

/-- The compiled typed run of a sequence. -/
def Prog.trunC : {Γ Γ' : Ctx} → Prog C Γ Γ' → TStep C Γ Γ'
  | _, _, .nil => TRun.nil
  | _, _, .cons s P => TRun.seq (Stmt.trunC s) (Prog.trunC P)

end

/-- The typed run of a statement, by its recursor. -/
@[implemented_by Stmt.trunC]
def Stmt.trunR {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : TStep C Γ Γ' :=
  Stmt.rec (motive_1 := fun Γ Γ' _ => TStep C Γ Γ') (motive_2 := fun Γ Γ' _ => TStep C Γ Γ')
    (fun l r => TRun.assign l r) (fun i r => TRun.rebind i r) (fun i r => TRun.assignLocal i r)
    (fun p _ init => TRun.declLocal p init) (fun R _ init => TRun.declStorage R init)
    (fun op _ _ l r => TRun.opAssign op l r) (fun op _ l => TRun.incDec op l)
    (fun i op _ l _ => TRun.assignIncDec i op l) (fun b v _ => TRun.push b v)
    (fun b => TRun.pop b) (fun r a => TRun.transfer r a) (fun pv r a => TRun.send pv r a)
    (fun R _ init _ hm => TRun.declMem R init hm) (fun i r => TRun.rebindMem i r)
    (fun l p => TRun.assignFromMem l p) (fun l r => TRun.assignMem l r)
    (fun l => TRun.delete l) (fun p _ => TRun.deleteMem p) (fun l n h => TRun.assignNew l n h)
    (fun c thn els ihThn ihEls => TRun.ite c thn.ext ihThn els.ext ihEls)
    (fun c => TRun.require c) (fun c => TRun.assert c) (fun _ => .error .revert)
    (fun _ args ret body ih => TRun.call args ret body.ext ih)
    (fun call rets ok err code pnc other ihOk ihErr ihPnc ihOther =>
      TRun.tryCall call rets ok.ext ihOk err.ext ihErr code pnc.ext ihPnc other.ext ihOther)
    (fun _ c body ih => TRun.loop c body.ext ih) (fun body ih => TRun.block body.ext ih)
    TRun.nil (fun _ _ ihS ihP => TRun.seq ihS ihP) s

/-- The typed run of a sequence, by its recursor. -/
@[implemented_by Prog.trunC]
def Prog.trunR {Γ Γ' : Ctx} (P : Prog C Γ Γ') : TStep C Γ Γ' :=
  Prog.rec (motive_1 := fun Γ Γ' _ => TStep C Γ Γ') (motive_2 := fun Γ Γ' _ => TStep C Γ Γ')
    (fun l r => TRun.assign l r) (fun i r => TRun.rebind i r) (fun i r => TRun.assignLocal i r)
    (fun p _ init => TRun.declLocal p init) (fun R _ init => TRun.declStorage R init)
    (fun op _ _ l r => TRun.opAssign op l r) (fun op _ l => TRun.incDec op l)
    (fun i op _ l _ => TRun.assignIncDec i op l) (fun b v _ => TRun.push b v)
    (fun b => TRun.pop b) (fun r a => TRun.transfer r a) (fun pv r a => TRun.send pv r a)
    (fun R _ init _ hm => TRun.declMem R init hm) (fun i r => TRun.rebindMem i r)
    (fun l p => TRun.assignFromMem l p) (fun l r => TRun.assignMem l r)
    (fun l => TRun.delete l) (fun p _ => TRun.deleteMem p) (fun l n h => TRun.assignNew l n h)
    (fun c thn els ihThn ihEls => TRun.ite c thn.ext ihThn els.ext ihEls)
    (fun c => TRun.require c) (fun c => TRun.assert c) (fun _ => .error .revert)
    (fun _ args ret body ih => TRun.call args ret body.ext ih)
    (fun call rets ok err code pnc other ihOk ihErr ihPnc ihOther =>
      TRun.tryCall call rets ok.ext ihOk err.ext ihErr code pnc.ext ihPnc other.ext ihOther)
    (fun _ c body ih => TRun.loop c body.ext ih) (fun body ih => TRun.block body.ext ih)
    TRun.nil (fun _ _ ihS ihP => TRun.seq ihS ihP) P

/-- The typed run of a statement from `σ`: the state it leaves, or how it
halts. -/
abbrev Stmt.trun {Γ Γ' : Ctx} (σ : TState C Γ) (s : Stmt C Γ Γ') : TRes (Out C σ.H Γ') :=
  s.trunR σ

/-- The typed run of a sequence from `σ`. -/
abbrev Prog.trun {Γ Γ' : Ctx} (σ : TState C Γ) (P : Prog C Γ Γ') : TRes (Out C σ.H Γ') :=
  P.trunR σ

mutual

theorem Stmt.trunR_eq : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → Stmt.trunR s = Stmt.trunC s
  | _, _, .ite c thn els => by
    show TRun.ite c thn.ext thn.trunR els.ext els.trunR =
      TRun.ite c thn.ext thn.trunC els.ext els.trunC
    rw [Prog.trunR_eq thn, Prog.trunR_eq els]
  | _, _, .call f args ret body => by
    show TRun.call args ret body.ext body.trunR = TRun.call args ret body.ext body.trunC
    rw [Prog.trunR_eq body]
  | _, _, .tryCall call rets ok err code pnc other => by
    show TRun.tryCall call rets ok.ext ok.trunR err.ext err.trunR code pnc.ext pnc.trunR
        other.ext other.trunR =
      TRun.tryCall call rets ok.ext ok.trunC err.ext err.trunC code pnc.ext pnc.trunC
        other.ext other.trunC
    rw [Prog.trunR_eq ok, Prog.trunR_eq err, Prog.trunR_eq pnc, Prog.trunR_eq other]
  | _, _, .loop a c body => by
    show TRun.loop c body.ext body.trunR = TRun.loop c body.ext body.trunC
    rw [Prog.trunR_eq body]
  | _, _, .block body => by
    show TRun.block body.ext body.trunR = TRun.block body.ext body.trunC
    rw [Prog.trunR_eq body]
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .declLocal ..
  | _, _, .declStorage .. | _, _, .opAssign .. | _, _, .incDec .. | _, _, .assignIncDec ..
  | _, _, .push .. | _, _, .pop .. | _, _, .transfer .. | _, _, .send .. | _, _, .declMem ..
  | _, _, .rebindMem .. | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete ..
  | _, _, .deleteMem .. | _, _, .assignNew .. | _, _, .require .. | _, _, .assert ..
  | _, _, .revert => rfl

theorem Prog.trunR_eq : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.trunR P = Prog.trunC P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    show TRun.seq s.trunR P.trunR = TRun.seq s.trunC P.trunC
    rw [Stmt.trunR_eq s, Prog.trunR_eq P]

end

/-! ### Equations -/

section Equations

variable {Γ : Ctx}

/-- How a typed result halts, if it does. -/
def TRes.halt? {α : Type} : TRes α → Option THalt
  | .ok _ => none
  | .error h => some h

theorem Prog.trun_nil (σ : TState C Γ) :
    Prog.trun σ (.nil : Prog C Γ Γ) = .ok ⟨σ, List.prefix_refl _⟩ := rfl

/-- A sequence whose first statement runs to `o` runs the rest from `o`'s
state. -/
theorem Prog.trun_cons_ok {Γ₁ Γ₂ : Ctx} {σ : TState C Γ} {o : Out C σ.H Γ₁} {s : Stmt C Γ Γ₁}
    {P : Prog C Γ₁ Γ₂} (h : s.trun σ = .ok o) :
    Prog.trun σ (.cons s P) = (Prog.trun o.st P).map fun o' => ⟨o'.st, o.ext.trans o'.ext⟩ := by
  show TRun.seq s.trunR P.trunR σ = _
  simp only [TRun.seq, Stmt.trun] at h ⊢
  rw [h]

theorem Stmt.trun_loop {Γ₁ : Ctx} (σ : TState C Γ) (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) :
    Stmt.trun σ (.loop a c body) =
      TLoop.run (fun o : Out C σ.H Γ => (Prog.trun o.st body).map
          fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
        (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩ := rfl

end Equations

/-! ## Examples

`Semantics/Core.lean`'s runs, on typed states: the storage the contract
deploys with, no memory, no locals. -/

section Examples

/-- A failing guard reverts. -/
example : (Prog.trun (TState.ofStorage Storage.standardExample) guardLowCore).halt? =
    some .revert := by
  decide +kernel

/-- A failing assertion panics. -/
example : (Prog.trun (TState.ofStorage Storage.standardExample) assertLowCore).halt? =
    some .panic := by
  decide +kernel

/-- solc's order of `++` inside an expression. -/
example : (Prog.trun (TState.ofStorage Storage.testSuite) incOrderCore).halt? = none := by
  decide +kernel

example : (Prog.trun (TState.ofStorage Storage.testSuite) indexOrderCore).halt? = none := by
  decide +kernel

/-- The calls of `CallsExample`: `addTwo(3)` is `5`, `larger(5, 7)` is `7`. -/
example : (match Prog.trun (TState.ofStorage (Storage.init CallsExample)) callsCore with
    | .ok o => some ((TEnv.get .here o.st.env : PrimTy.uint.Denote).1,
        (TEnv.get (.there .here) o.st.env : PrimTy.uint.Denote).1)
    | .error _ => none) = some (7, 5) := by
  decide +kernel

end Examples

end Core

end Solidity
