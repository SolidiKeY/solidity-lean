import Solidity.Semantics.State
import Solidity.Semantics.Ops

/-!
# The typed run

The run on typed values (`docs/intrinsic.md`, "M4 lane", wiring items 3
and 4): a state is a `State` (typed storage, a
heap and its typing, the locals typed over it), a storage path resolves to
an `SRef` (an index by `SRef.index`, at its key type), a
memory path to a heap reference read through `Heap.field`/`Heap.index`, and
an operator is `BinOp.evalT`/`UnOp.evalT`.  A run ends in a state or halts
with `THalt`: `revert`, `panic`, `diverge` or `exhausted`; there is no
`stuck`.

A dynamic array holds fewer than `2^256` elements (`SVal.array`, `MObj`), so
a length is a `uint` (`Storage.len`, `Heap.lenU`).  A push onto `2^256 - 1`
elements exhausts the resources: the run halts with `exhausted`
(`Storage.full`, decision 15), which both modalities accept, as KeY, which
models no gas, reads every run that runs out of it (`docs/solc-alignment.md`,
"Array lengths").

The heap only grows, and a call sets its caller's locals aside while the body
runs, so each step returns its state with the extension of the heap typing
(`Out`): the caller's locals are weakened along it when the call returns.

Each statement's step is one function
(`TRun.*`) given its sub-programs' runs, `Stmt.run`/`Prog.run` are the
recursor over them (`Stmt.runR`, Gate G0 conditions 1 and 2) with a
`match` twin for the compiler (`Stmt.runC`, linked by `Stmt.runR_eq`).
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


open Semantics (Selector lookupBy setBy ExtKey ExtResult structDef)

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

/-- A bind of a result that returns: the continuation. -/
theorem ok_bind {ε α β : Type} (a : α) (k : α → Except ε β) :
    (Except.ok a : Except ε α) >>= k = k a := rfl

/-- A bind of a result that halts: the halt. -/
theorem error_bind {ε α β : Type} (e : ε) (k : α → Except ε β) :
    (Except.error e : Except ε α) >>= k = .error e := rfl

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
  st : State C Γ
  ext : H <+: st.H

/-- A state over a grown heap, its extension, and a value over its typing. -/
structure Grew (C : Contract) (Γ : Ctx) (H : HTy) (α : HTy → Type) where
  st : State C Γ
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

namespace State

variable {Γ : Ctx}

/-- The locals replaced, in another context. -/
def withEnv {Δ : Ctx} (σ : State C Γ) (e : TEnv C σ.H Δ) : State C Δ :=
  { storage := σ.storage, H := σ.H, heap := σ.heap, env := e, net := σ.net,
    selfBalance := σ.selfBalance, tx := σ.tx }

/-- The objects replaced, at the same typing. -/
def withHeap (σ : State C Γ) (hp : Heap σ.H) : State C Γ := { σ with heap := hp }

/-- A grown heap adopted, with its extension (`adopt`). -/
def grow {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α) : Grew C Γ σ.H α :=
  ⟨(σ.adopt g).1, g.ext, g.val⟩

/-- A fresh default object (`allocDefault`), with the extension. -/
def allocDefaultG (σ : State C Γ) (R : RefTy) (h : (Ty.ref R).mapFree = true) :
    Grew C Γ σ.H (MVal · (.ref R)) :=
  σ.grow (σ.heap.allocDefault R h)

/-- A storage value copied into fresh objects (`copyStToM`), with the
extension. -/
def copyStToMG {T : Ty} (σ : State C Γ) (v : SVal T) (h : T.mapFree = true) :
    Grew C Γ σ.H (MVal · T) :=
  σ.grow (v.copyStToM σ.heap h)

/-- A value of the environment. -/
def envVal (σ : State C Γ) : EnvKey → PrimTy.uint.Denote
  | .msgSender => σ.tx.msgSender
  | .msgValue => σ.tx.msgValue
  | .timestamp => σ.tx.timestamp
  | .selfBalance => σ.selfBalance
  | .selfAddress => σ.tx.selfAddress

/-- `amt` paid to `addr` on the ledger (`State.pay`): nothing booked for the
contract itself. -/
def pay (σ : State C Γ) (addr : PrimTy.uint.Denote) (amt : Int) : State C Γ :=
  { σ with net := if addr.1 = σ.tx.selfAddress.1 then σ.net
      else setBy addr ((lookupBy addr σ.net).getD 0 - amt) σ.net }

/-- A state with no locals and no memory, over a storage. -/
def ofStorage (st : Storage C) : State C [] :=
  { storage := st, H := [], heap := Heap.empty, env := () }

end State

/-! ## Memory addresses -/

/-- A memory location, resolved: a struct's member, or an element. -/
inductive MAddr (H : HTy) : Ty → Type where
  | field {s f : Name} {T : Ty} (r : HRef H (.struct s)) (h : lookupBy f (structDef s) = some T) :
      MAddr H T
  | index {R : RefTy} {E : Ty} (r : HRef H R) (a : ArrTy R E) (i : PrimTy.uint.Denote) : MAddr H E

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
evaluated. -/
def _root_.Solidity.BinOp.shortT : (op : BinOp) → {p : PrimTy} → p.Denote → Option (op.ret p).Denote
  | .and, .bool, x => if boolT x then none else some (false : Bool)
  | .or, .bool, x => if boolT x then some (true : Bool) else none
  | _, _, _ => none

/-- `a ⊕= b` at a numeric type: the operator on the integers, then the range
check. -/
def compoundT (op : BinOp) (p : PrimTy) (x y : Int) : Option p.Denote :=
  (BinOp.arithInt op x y).bind p.ofInt?

/-- `x++`/`x--` at a numeric type. -/
def bumpT (op : IncDec) (p : PrimTy) (x : Int) : Option p.Denote :=
  p.ofInt? (if op.isIncrement then x + 1 else x - 1)

/-- `n` elements, `n` a `uint`: below the bound. -/
theorem newArr_lt {E : Ty} (n : PrimTy.uint.Denote) (v : SVal E) :
    (List.replicate n.1.toNat v).length < 2 ^ 256 := by
  have h := n.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  rw [List.length_replicate]
  omega

/-- What `new R(n)` allocates, as the storage value it is a copy of: `n`
default elements. -/
def newArrT : (R : RefTy) → PrimTy.uint.Denote → R.newArrOk = true → SVal (.ref R)
  | .array E, n, _ => .array (SVec.ofList (List.replicate n.1.toNat (SVal.dflt E))) .nil
      (newArr_lt n _)
  | .struct _, _, h | .fixed .., _, h | .mapping .., _, h =>
    absurd h (by simp only [RefTy.newArrOk, Bool.false_eq_true, not_false_eq_true])

/-! ## Expressions -/

section Eval

variable {Γ : Ctx}

/-- The value a simple value denotes. -/
def Simple.evalT (σ : State C Γ) : {p : PrimTy} → Simple C Γ p → p.Denote
  | p, .lit n h => PrimTy.ofLit p n h
  | _, .bool b => (b : Bool)
  | _, .local i => TEnv.get i σ.env
  | _, .env k hp => hp ▸ σ.envVal k

mutual

/-- The storage reference a path denotes: an unset alias reverts. -/
def SPath.resolveT (σ : State C Γ) : {T : Ty} → SPath C Γ T → TRes (SRef C T)
  | _, .alias i =>
    match (TEnv.get i σ.env : Option (SRef C _)) with
    | some r => .ok r
    | none => .error .revert
  | _, .loc l => l.resolveT σ

def Loc.resolveT (σ : State C Γ) : {T : Ty} → Loc C Γ T → TRes (SRef C T)
  | _, .root r h => .ok (SRef.ofRoot r h)
  | _, .field b _ h => do
    let r ← b.resolveT σ
    pure (r.field h)
  | _, .index it b i => do
    let r ← b.resolveT σ
    let k ← i.evalT σ
    TRes.ofOpt (σ.storage.checkIndex r it k)
    pure (r.index it k)

/-- The slot a memory path holds: an unset memory local reverts, as an
unset alias does (decision 17'). -/
def MPath.mvalT (σ : State C Γ) : {T : Ty} → MPath C Γ T → TRes (MVal σ.H T)
  | _, .var i _ =>
    match (TEnv.get i σ.env : Option (HRef σ.H _)) with
    | some r => .ok r
    | none => .error .revert
  | _, .loc l => do TRes.ofOpt (σ.heap.readAddr (← l.addrT σ))

/-- The address of a memory location: the object, then the index. -/
def MLoc.addrT (σ : State C Γ) : {T : Ty} → MLoc C Γ T → TRes (MAddr σ.H T)
  | _, .field b _ h => do
    let r ← b.mvalT σ
    pure (.field r h)
  | _, .index a b i => do
    let r ← b.mvalT σ
    let k ← i.evalT σ
    pure (.index r a k)

/-- The value a value expression denotes. -/
def Val.evalT (σ : State C Γ) : {p : PrimTy} → Val C Γ p → TRes p.Denote
  | _, .simple s => .ok (s.evalT σ)
  | _, .read l => do
    let r ← l.resolveT σ
    let v ← TRes.ofOpt (σ.storage.find r)
    pure v.view
  | _, .binop op h hq a b => do
    let x ← a.evalT σ
    match op.shortT x with
    | some y => pure (hq ▸ y)
    | none => do
      let y ← b.evalT σ
      hq ▸ TRes.ofOpt (op.evalT h x y)
  | _, .unop op h hq a => do
    let x ← a.evalT σ
    hq ▸ TRes.ofOpt (op.evalT h x)
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
  | _, .modular op a b k => do
    let x ← a.evalT σ
    let y ← b.evalT σ
    let m ← k.evalT σ
    TRes.ofOpt (op.evalT x y m)

end

/-- The storage value a source stores. -/
def Src.valueT (σ : State C Γ) {T : Ty} : Src C Γ T → TRes (SVal T)
  | .val v => do pure (.prim (← v.evalT σ))
  | .copy p _ => do
    let r ← p.resolveT σ
    TRes.ofOpt (σ.storage.find r)
  | .fixedCopy p shape _ => do
    let r ← p.resolveT σ
    let v ← TRes.ofOpt (σ.storage.find r)
    pure (shape.apply v)
  | .copyMem p => do
    pure (MVal.copyMToSt σ.heap (← p.mvalT σ))

/-- The slot a memory source writes. -/
def MSrc.mvalT (σ : State C Γ) {T : Ty} : MSrc C Γ T → TRes (MVal σ.H T)
  | .val v => v.evalT σ
  | .ref p => p.mvalT σ

/-- The storage a storage alias's right-hand side leaves (a push grows an
array), and the reference it names. -/
def ARhs.evalT (σ : State C Γ) {R : RefTy} : ARhs C Γ R → TRes (Storage C × SRef C (.ref R))
  | .path p => do pure (σ.storage, ← p.resolveT σ)
  | .push b _ => do
    let r ← b.resolveT σ
    if σ.storage.full r then .error .exhausted else
    let (st, n) ← TRes.ofOpt (σ.storage.pushPlace r)
    pure (st, r.index (.arr .dyn) n)

/-- The object a memory right-hand side names, and the state its allocation
leaves. -/
def MRhs.evalT (σ : State C Γ) {R : RefTy} : MRhs C Γ R → TRes (Grew C Γ σ.H (HRef · R))
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
def opStoreT (σ : State C Γ) (op : BinOp) {p : PrimTy} (r : SRef C (.prim p)) (v : p.Denote) :
    TRes (Out C σ.H Γ) := do
  let old ← TRes.ofOpt (σ.storage.find r)
  let new ← TRes.ofOpt (compoundT op p (PrimTy.key (SVal.view old)) (PrimTy.key v))
  let st ← TRes.ofOpt (σ.storage.save r (.prim new))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

/-- `a ⊕= v` at a memory address. -/
def opMemT (σ : State C Γ) (op : BinOp) {p : PrimTy} (a : MAddr σ.H (.prim p)) (v : p.Denote) :
    TRes (Out C σ.H Γ) := do
  let old ← TRes.ofOpt (σ.heap.readAddr a)
  let new ← TRes.ofOpt (compoundT op p (PrimTy.key (p := p) old) (PrimTy.key v))
  let hp ← TRes.ofOpt (σ.heap.writeAddr a new)
  pure ⟨σ.withHeap hp, List.prefix_refl _⟩

/-- A compound assignment's write of `v` into its target. -/
def OpLoc.storeT (σ : State C Γ) (op : BinOp) : {p : PrimTy} → OpLoc C Γ p → p.Denote →
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
def bumpStoreT (σ : State C Γ) (op : IncDec) {p : PrimTy} (r : SRef C (.prim p)) :
    TRes (Out C σ.H Γ × p.Denote) := do
  let old ← TRes.ofOpt (σ.storage.find r)
  let new ← TRes.ofOpt (bumpT op p (PrimTy.key (SVal.view old)))
  let st ← TRes.ofOpt (σ.storage.save r (.prim new))
  pure (⟨σ.withStorage st, List.prefix_refl _⟩, if op.isPre then new else SVal.view old)

/-- `x++` at a memory address. -/
def bumpMemT (σ : State C Γ) (op : IncDec) {p : PrimTy} (a : MAddr σ.H (.prim p)) :
    TRes (Out C σ.H Γ × p.Denote) := do
  let old ← TRes.ofOpt (σ.heap.readAddr a)
  let new ← TRes.ofOpt (bumpT op p (PrimTy.key (p := p) old))
  let hp ← TRes.ofOpt (σ.heap.writeAddr a new)
  pure (⟨σ.withHeap hp, List.prefix_refl _⟩, if op.isPre then new else old)

/-- `l++`: the state it leaves, and its value. -/
def OpLoc.bumpT (σ : State C Γ) (op : IncDec) : {p : PrimTy} → OpLoc C Γ p →
    TRes (Out C σ.H Γ × p.Denote)
  | p, .local i => do
    let old : p.Denote := TEnv.get i σ.env
    let new ← TRes.ofOpt (Solidity.bumpT op p (PrimTy.key old))
    pure (⟨σ.setLocal i new, List.prefix_refl _⟩, if op.isPre then new else old)
  | _, .root r h => bumpStoreT σ op (SRef.ofRoot r h)
  | _, .field b f h => do bumpStoreT σ op (← (Loc.field b f h).resolveT σ)
  | _, .index it b i => do bumpStoreT σ op (← (Loc.index it b (.simple i)).resolveT σ)
  | _, .mfield b f h => do bumpMemT σ op (← (MLoc.field b f h).addrT σ)
  | _, .mindex a b i => do bumpMemT σ op (← (MLoc.index a b (.simple i)).addrT σ)

/-- `pv = a.send(v);` with both evaluated (`sendT`): a payment refused books
nothing and sets `pv` to `false`. -/
def sendT (σ : State C Γ) (pv : Idx Γ (.val .bool)) (addr amt : PrimTy.uint.Denote) : Out C σ.H Γ :=
  match lookupBy (sendKey addr amt) σ.tx.ext with
  | none | some (.ok _) => ⟨(σ.pay addr amt.1).setLocal pv (true : Bool), List.prefix_refl _⟩
  | some _ => ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩

/-- The call as it is made: its bounded receiver and arguments at their Solidity types. -/
def ExtCall.keyT (σ : State C Γ) (c : ExtCall C Γ) : ExtKey :=
  ⟨c.addr.evalT σ, c.fn, c.args.map fun a => Semantics.CallValue.ofTyped (a.2.evalT σ)⟩

/-- A call's arguments, each read in the caller's state, in order. -/
def Args.evalT (σ : State C Γ) : {ps : Ctx} → Args C Γ ps → TRes (TEnv C σ.H ps)
  | _, as => Args.casesOn (motive := fun ps _ => TRes (TEnv C σ.H ps)) as (pure ())
      (fun as _ _ e => do
        let r ← Args.evalT σ as
        let v ← e.evalT σ
        pure (v, r))
      (fun as _ _ e => do
        let r ← Args.evalT σ as
        let v ← e.resolveT σ
        pure (some v, r))
      (fun as _ _ e => do
        let r ← Args.evalT σ as
        let v ← e.mvalT σ
        pure (some v, r))
  termination_by structural _ as => as

end Eval

/-- The return variables at their defaults. -/
def Binders.defaultsT {H : HTy} : {ρ : Ctx} → Binders ρ → TEnv C H ρ
  | _, bs => Binders.casesOn (motive := fun ρ _ => TEnv C H ρ) bs ()
      (fun bs p _ => (PrimTy.dflt p, Binders.defaultsT bs))
  termination_by structural _ bs => bs

/-- The locals an external call's data binds, read back at their types, and
the data left: too short, or a word not of its local's type, reverts. -/
def Binders.decodeT {H : HTy} :
    {ρ : Ctx} → Binders ρ → List Semantics.Word → TRes (TEnv C H ρ × List Semantics.Word)
  | _, bs => Binders.casesOn
      (motive := fun ρ _ => List Semantics.Word → TRes (TEnv C H ρ × List Semantics.Word)) bs
      (fun vs => pure ((), vs))
      (fun bs p _ vs => do
        let (e, rest) ← Binders.decodeT bs vs
        match rest with
        | v :: rest =>
          match PrimTy.ofWord? p v with
          | some x => pure ((x, e), rest)
          | none => .error .revert
        | [] => .error .revert)
  termination_by structural _ bs => bs

/-- The `Panic` code bound, if the clause names it: a `uint256`, so every
word decodes. -/
def CodeBinder.decodeT {H : HTy} {κ : Ctx} (code : CodeBinder κ) (c : Semantics.Word) :
    TEnv C H κ :=
  CodeBinder.casesOn (motive := fun κ _ => TEnv C H κ) code () (fun _ => (c, ()))

/-- Entering a call: its return variables at their defaults on the frame's
parameters (a memory return a fresh default object). -/
def CallRet.enterT {Γ : Ctx} {rs Γ' : Ctx} (ret : CallRet Γ rs Γ') {ps : Ctx}
    (τ : State C ps) : Out C τ.H (rs ++ ps) :=
  CallRet.casesOn (motive := fun rs _ _ => Out C τ.H (rs ++ ps)) ret
    ⟨τ, List.prefix_refl _⟩
    (fun p _ _ => ⟨τ.push (t := .val p) (PrimTy.dflt p), List.prefix_refl _⟩)
    (fun {rs} bs => ⟨τ.withEnv (TEnv.append rs (Binders.defaultsT bs) τ.env), List.prefix_refl _⟩)
    (fun R _ _ hm =>
      let g := τ.allocDefaultG R hm
      ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩)
    (fun R _ => ⟨τ.push (t := .alias R) Option.none, List.prefix_refl _⟩)

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
    (fun _ _ r => (r.1, e))

/-! ## Loops

A loop on typed results: the condition is a `Bool`. -/

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

/-- **Induction over a loop's run**: `P` holds of the first state and of
every state an iteration from a state in `P` goes on in, and `Q` of every
outcome an iteration from a state in `P` is done with, and of a divergence:
then `Q` holds of the loop's run. -/
theorem run_induct {body : α → TRes α} {c : α → TRes Bool} {P : α → Prop} {Q : TRes α → Prop}
    {σ : α} (h0 : P σ)
    (hstep : ∀ τ, P τ →
      match step body c τ with
      | .inl τ' => P τ'
      | .inr r => Q r)
    (hdiv : Q (.error .diverge)) : Q (run body c σ) := by
  have key : ∀ (n : Nat) (τ : α) (r : TRes α), P τ → iterN body c n τ = .inr r → Q r := by
    intro n
    induction n with
    | zero => intro τ r _ h; exact nomatch h
    | succ n ih =>
      intro τ r hp h
      have hs := hstep τ hp
      simp only [iterN] at h
      revert hs h
      cases step body c τ with
      | inl τ' => exact fun he hp => ih τ' r hp he
      | inr r' =>
        intro he hp
        cases (show Sum.inr r' = (Sum.inr r : α ⊕ TRes α) from he)
        exact hp
  unfold run
  split
  · rename_i hex
    obtain ⟨n, hn⟩ := Classical.choose_spec hex
    exact key n σ _ h0 hn
  · exact hdiv

end TLoop

/-! ## Statements -/

/-- A step: from a state, the state it leaves over a grown heap. -/
abbrev TStep (C : Contract) (Γ Γ' : Ctx) : Type := (σ : State C Γ) → TRes (Out C σ.H Γ')

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

/-- `y = values.push();`: the array grown as `values.push();` grows it, `y`
the default the cleared slot holds. -/
def assignLocalPush {p : PrimTy} (i : Idx Γ (.val p)) (b : SPath C Γ (.array (.prim p))) :
    TStep C Γ Γ := fun σ => do
  let o ← TRun.push b none σ
  pure ⟨o.st.setLocal i (PrimTy.dflt p), o.ext⟩

/-- `values.push() += e`: RHS first, receiver once, then reset/append and
checked arithmetic. Capacity exhaustion precedes arithmetic failure. -/
def pushOpAssign {p : PrimTy} (op : BinOp) (b : SPath C Γ (.array (.prim p)))
    (rhs : Val C Γ p) : TStep C Γ Γ := fun σ => do
  let value ← rhs.evalT σ
  let ref ← b.resolveT σ
  if σ.storage.full ref then .error .exhausted else
  let (st, index) ← TRes.ofOpt (σ.storage.pushPlace ref)
  opStoreT (σ.withStorage st) op (ref.index (.arr .dyn) index) value

/-- `++values.push()` and `values.push()++` as statements: append/reset,
then bump the new slot; the prefix/postfix value is discarded. -/
def pushIncDec {p : PrimTy} (op : IncDec) (b : SPath C Γ (.array (.prim p))) :
    TStep C Γ Γ := fun σ => do
  let ref ← b.resolveT σ
  if σ.storage.full ref then .error .exhausted else
  let (st, index) ← TRes.ofOpt (σ.storage.pushPlace ref)
  pure (← bumpStoreT (σ.withStorage st) op (ref.index (.arr .dyn) index)).1

def pop {E : Ty} (b : SPath C Γ (.array E)) : TStep C Γ Γ := fun σ => do
  let ref ← b.resolveT σ
  let st ← TRes.ofOpt (σ.storage.pop E.isMapping ref)
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

def transfer (r a : Val C Γ .uint) : TStep C Γ Γ := fun σ => do
  let addr ← r.evalT σ
  let amt ← a.evalT σ
  pure ⟨σ.pay addr amt.1, List.prefix_refl _⟩

def send (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) : TStep C Γ Γ := fun σ => do
  let addr ← r.evalT σ
  let amt ← a.evalT σ
  pure (sendT σ pv addr amt)

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

/-- `delete` at a memory address: a word to its default, a
reference to a fresh default object. -/
def clearT (σ : State C Γ) : {T : Ty} → MAddr σ.H T → T.mapFree = true → TRes (Out C σ.H Γ)
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

/-- The array operation at its already resolved receiver alias. -/
def receiverOp {E : Ty} (op : ReceiverOp C Γ E) (b : SPath C Γ (.array E)) : TStep C Γ Γ :=
  match op with
  | .push v _ => push b v
  | .pop => pop b

/-- A storage-returning receiver runs once, before its array operation reads
the source. The temporary return alias is dropped afterwards. -/
def callReceiver {ps Γf : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (h : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : TStep C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E) :
    TStep C Γ Γ := fun σ => do
  let o ← call args (.storage (.array E) r) h body σ
  let o' ← receiverOp (op.wk (.drop .refl)) (.alias .here) o.st
  pure ⟨o'.st.drop (.push .refl), o.ext.trans o'.ext⟩

/-- Complete a deferred operand at its already validated receiver; its temporary
locals end after the source has been read and copied. -/
def pushAfterPrefix {Γv : Ctx} {E : Ty} (h : Ext Γ Γv) (code : TStep C Γ Γv)
    (value : Src C Γv E) (ref : SRef C (.ref (.array E))) : TStep C Γ Γ := fun σ => do
  let a ← code σ
  let v ← value.valueT a.st
  if a.st.storage.full ref then .error .exhausted else
  let st ← TRes.ofOpt (a.st.storage.push ref fun _ => some v.strip)
  pure ⟨(a.st.withStorage st).drop h, a.ext⟩

/-- Validate a getter result before any deferred operand effect runs. -/
def afterReceiverPrefix {Γv : Ctx} {E : Ty} (he : Ext Γ Γv) (code : TStep C Γ Γv)
    (value : Src C Γv E) : TStep C (.alias (.array E) :: Γ) Γ := fun σ => do
  let ref ← SPath.resolveT σ (.alias .here)
  pushAfterPrefix he code value ref (σ.drop (.push .refl))

/-- `f().push(e)` with effects in `e`: getter once, validation before the
operand prefix, then the source snapshot and push at that fixed receiver. -/
def callReceiverPush {ps Γf Γv : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (hb : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : TStep C ([.alias (.array E)] ++ ps) Γf)
    (he : Ext Γ Γv) (code : TStep C Γ Γv) (value : Src C Γv E) : TStep C Γ Γ := fun σ => do
  let a ← call args (.storage (.array E) r) hb body σ
  (afterReceiverPrefix he code value a.st).map fun b => ⟨b.st, a.ext.trans b.ext⟩

/-- The `Panic` code a self-call that panics binds: the transaction's entry
for the call, `1` (a failed `assert`) without one. -/
def selfPanicCode (call : ExtCall C Γ) (σ : State C Γ) : Semantics.Word :=
  match lookupBy (call.keyT σ) σ.tx.ext with
  | some (.panic c) => c
  | _ => ⟨1, by decide⟩

/-- `try`: no code at address `0`, where the caller reverts; the contract's
own function run in a frame of its own when the receiver is the contract
itself and the elaborator found the callee (`self`, `docs/options.md` O8);
otherwise the clause the transaction's outcome picks.  Either way the
clause's locals are popped.  A self-call that reverts goes to the `Error`
clause when the transaction's entry says the call ends in `Error`, to the
catch-all otherwise (the model keeps no revert data); one that panics, to
the `Panic` clause with the entry's code, `1` without one; one that
exhausts or diverges halts the caller alike. -/
def tryCall {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : TStep C (ρ ++ Γ) Γ₁)
    (h₂ : Ext Γ Γ₂) (err : TStep C Γ Γ₂) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : TStep C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : TStep C Γ Γ₄) (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf)
    (sbody : TStep C (ρ ++ ps) Γf) (self : Bool) : TStep C Γ Γ := fun σ =>
  if (call.addr.evalT σ).1 = 0 then .error .revert else
  if self && decide ((call.addr.evalT σ).1 = σ.tx.selfAddress.1) then
    match TRun.call sargs (.rets rets) hs sbody σ with
    | .ok o => (ok o.st).map fun o' =>
      ⟨o'.st.drop ((Ext.append Γ ρ).trans h₁), o.ext.trans o'.ext⟩
    | .error .revert =>
      match lookupBy (call.keyT σ) σ.tx.ext with
      | some .error => (err σ).map fun o => ⟨o.st.drop h₂, o.ext⟩
      | _ => (other σ).map fun o => ⟨o.st.drop h₄, o.ext⟩
    | .error .panic =>
      (pnc (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) (selfPanicCode call σ)) σ.env))).map
        fun o => ⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩
    | .error e => .error e
  else
  match lookupBy (call.keyT σ) σ.tx.ext with
  | none => .error .revert
  | some (.ok vs) => do
    let (r, _) ← rets.decodeT (H := σ.H) vs
    (ok (σ.withEnv (TEnv.append ρ r σ.env))).map fun o =>
      ⟨o.st.drop ((Ext.append Γ ρ).trans h₁), o.ext⟩
  | some .error => (err σ).map fun o => ⟨o.st.drop h₂, o.ext⟩
  | some (.panic c) =>
    (pnc (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env))).map fun o =>
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
def Stmt.runC : {Γ Γ' : Ctx} → Stmt C Γ Γ' → TStep C Γ Γ'
  | _, _, .assign l r => TRun.assign l r
  | _, _, .rebind i r => TRun.rebind i r
  | _, _, .assignLocal i r => TRun.assignLocal i r
  | _, _, .declLocal p _ init => TRun.declLocal p init
  | _, _, .declStorage R _ init => TRun.declStorage R init
  | _, _, .opAssign op _ _ l r => TRun.opAssign op l r
  | _, _, .incDec op _ l => TRun.incDec op l
  | _, _, .pushOpAssign op _ _ b r => TRun.pushOpAssign op b r
  | _, _, .pushIncDec op _ b => TRun.pushIncDec op b
  | _, _, .assignIncDec i op _ l _ => TRun.assignIncDec i op l
  | _, _, .assignLocalPush i b => TRun.assignLocalPush i b
  | _, _, .push b v _ => TRun.push b v
  | _, _, .pop b => TRun.pop b
  | _, _, .transfer r a => TRun.transfer r a
  | _, _, .send pv r a _ => TRun.send pv r a
  | _, _, .declMem R _ init _ hm => TRun.declMem R init hm
  | _, _, .rebindMem i r => TRun.rebindMem i r
  | _, _, .assignFromMem l p => TRun.assignFromMem l p
  | _, _, .assignMem l r => TRun.assignMem l r
  | _, _, .delete l => TRun.delete l
  | _, _, .deleteMem p _ => TRun.deleteMem p
  | _, _, .assignNew l n h => TRun.assignNew l n h
  | _, _, .ite c thn els => TRun.ite c thn.ext (Prog.runC thn) els.ext (Prog.runC els)
  | _, _, .require c => TRun.require c
  | _, _, .assert c => TRun.assert c
  | _, _, .revert => fun _ => .error .revert
  | _, _, .assumeFalse => fun _ => .error .exhausted
  | _, _, .call _ args ret body => TRun.call args ret body.ext (Prog.runC body)
  | _, _, .callReceiver _ args r body op => TRun.callReceiver args r body.ext (Prog.runC body) op
  | _, _, .callReceiverPush _ args r body code value =>
    TRun.callReceiverPush args r body.ext (Prog.runC body) code.ext (Prog.runC code) value
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self =>
    TRun.tryCall call rets ok.ext (Prog.runC ok) err.ext (Prog.runC err) code pnc.ext
      (Prog.runC pnc) other.ext (Prog.runC other) sargs sbody.ext (Prog.runC sbody) self
  | _, _, .loop _ c body => TRun.loop c body.ext (Prog.runC body)
  | _, _, .block body => TRun.block body.ext (Prog.runC body)
  | _, _, .callRec _ _ args ret body => TRun.call args ret (body ()).ext (Prog.runC (body ()))

/-- The compiled typed run of a sequence. -/
def Prog.runC : {Γ Γ' : Ctx} → Prog C Γ Γ' → TStep C Γ Γ'
  | _, _, .nil => TRun.nil
  | _, _, .cons s P => TRun.seq (Stmt.runC s) (Prog.runC P)

end

/-- The typed run of a statement, by its recursor. -/
@[implemented_by Stmt.runC]
def Stmt.runR {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : TStep C Γ Γ' :=
  Stmt.rec (motive_1 := fun Γ Γ' _ => TStep C Γ Γ') (motive_2 := fun Γ Γ' _ => TStep C Γ Γ')
    (fun l r => TRun.assign l r) (fun i r => TRun.rebind i r) (fun i r => TRun.assignLocal i r)
    (fun p _ init => TRun.declLocal p init) (fun R _ init => TRun.declStorage R init)
    (fun op _ _ l r => TRun.opAssign op l r) (fun op _ l => TRun.incDec op l)
    (fun i op _ l _ => TRun.assignIncDec i op l) (fun i b => TRun.assignLocalPush i b)
    (fun b v _ => TRun.push b v)
    (fun b => TRun.pop b) (fun r a => TRun.transfer r a) (fun pv r a _ => TRun.send pv r a)
    (fun R _ init _ hm => TRun.declMem R init hm) (fun i r => TRun.rebindMem i r)
    (fun l p => TRun.assignFromMem l p) (fun l r => TRun.assignMem l r)
    (fun l => TRun.delete l) (fun p _ => TRun.deleteMem p) (fun l n h => TRun.assignNew l n h)
    (fun c thn els ihThn ihEls => TRun.ite c thn.ext ihThn els.ext ihEls)
    (fun c => TRun.require c) (fun c => TRun.assert c) (fun _ => .error .revert)
    (fun _ => .error .exhausted)
    (fun _ args ret body ih => TRun.call args ret body.ext ih)
    (fun call rets ok err code pnc other sargs sbody self ihOk ihErr ihPnc ihOther ihSelf =>
      TRun.tryCall call rets ok.ext ihOk err.ext ihErr code pnc.ext ihPnc other.ext ihOther
        sargs sbody.ext ihSelf self)
    (fun _ c body ih => TRun.loop c body.ext ih) (fun body ih => TRun.block body.ext ih)
    (fun op _ _ b r => TRun.pushOpAssign op b r) (fun op _ b => TRun.pushIncDec op b)
    (fun _ args r body op ih => TRun.callReceiver args r body.ext ih op)
    (fun _ args r body code value ihBody ihCode =>
      TRun.callReceiverPush args r body.ext ihBody code.ext ihCode value)
    (fun _ _ args ret body ih => TRun.call args ret (body ()).ext (ih ()))
    TRun.nil (fun _ _ ihS ihP => TRun.seq ihS ihP) s

/-- The typed run of a sequence, by its recursor. -/
@[implemented_by Prog.runC]
def Prog.runR {Γ Γ' : Ctx} (P : Prog C Γ Γ') : TStep C Γ Γ' :=
  Prog.rec (motive_1 := fun Γ Γ' _ => TStep C Γ Γ') (motive_2 := fun Γ Γ' _ => TStep C Γ Γ')
    (fun l r => TRun.assign l r) (fun i r => TRun.rebind i r) (fun i r => TRun.assignLocal i r)
    (fun p _ init => TRun.declLocal p init) (fun R _ init => TRun.declStorage R init)
    (fun op _ _ l r => TRun.opAssign op l r) (fun op _ l => TRun.incDec op l)
    (fun i op _ l _ => TRun.assignIncDec i op l) (fun i b => TRun.assignLocalPush i b)
    (fun b v _ => TRun.push b v)
    (fun b => TRun.pop b) (fun r a => TRun.transfer r a) (fun pv r a _ => TRun.send pv r a)
    (fun R _ init _ hm => TRun.declMem R init hm) (fun i r => TRun.rebindMem i r)
    (fun l p => TRun.assignFromMem l p) (fun l r => TRun.assignMem l r)
    (fun l => TRun.delete l) (fun p _ => TRun.deleteMem p) (fun l n h => TRun.assignNew l n h)
    (fun c thn els ihThn ihEls => TRun.ite c thn.ext ihThn els.ext ihEls)
    (fun c => TRun.require c) (fun c => TRun.assert c) (fun _ => .error .revert)
    (fun _ => .error .exhausted)
    (fun _ args ret body ih => TRun.call args ret body.ext ih)
    (fun call rets ok err code pnc other sargs sbody self ihOk ihErr ihPnc ihOther ihSelf =>
      TRun.tryCall call rets ok.ext ihOk err.ext ihErr code pnc.ext ihPnc other.ext ihOther
        sargs sbody.ext ihSelf self)
    (fun _ c body ih => TRun.loop c body.ext ih) (fun body ih => TRun.block body.ext ih)
    (fun op _ _ b r => TRun.pushOpAssign op b r) (fun op _ b => TRun.pushIncDec op b)
    (fun _ args r body op ih => TRun.callReceiver args r body.ext ih op)
    (fun _ args r body code value ihBody ihCode =>
      TRun.callReceiverPush args r body.ext ihBody code.ext ihCode value)
    (fun _ _ args ret body ih => TRun.call args ret (body ()).ext (ih ()))
    TRun.nil (fun _ _ ihS ihP => TRun.seq ihS ihP) P

/-- The typed run of a statement from `σ`: the state it leaves, or how it
halts. -/
abbrev Stmt.run {Γ Γ' : Ctx} (σ : State C Γ) (s : Stmt C Γ Γ') : TRes (Out C σ.H Γ') :=
  s.runR σ

/-- The typed run of a sequence from `σ`. -/
abbrev Prog.run {Γ Γ' : Ctx} (σ : State C Γ) (P : Prog C Γ Γ') : TRes (Out C σ.H Γ') :=
  P.runR σ

mutual

theorem Stmt.runR_eq : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → Stmt.runR s = Stmt.runC s
  | _, _, .ite c thn els => by
    show TRun.ite c thn.ext thn.runR els.ext els.runR =
      TRun.ite c thn.ext thn.runC els.ext els.runC
    rw [Prog.runR_eq thn, Prog.runR_eq els]
  | _, _, .call f args ret body => by
    show TRun.call args ret body.ext body.runR = TRun.call args ret body.ext body.runC
    rw [Prog.runR_eq body]
  | _, _, .callRec f d args ret body => by
    show TRun.call args ret (body ()).ext (body ()).runR =
      TRun.call args ret (body ()).ext (body ()).runC
    rw [Prog.runR_eq (body ())]
  | _, _, .callReceiver f args r body op => by
    show TRun.callReceiver args r body.ext body.runR op = TRun.callReceiver args r body.ext body.runC op
    rw [Prog.runR_eq body]
  | _, _, .callReceiverPush f args r body code value => by
    show TRun.callReceiverPush args r body.ext body.runR code.ext code.runR value =
      TRun.callReceiverPush args r body.ext body.runC code.ext code.runC value
    rw [Prog.runR_eq body, Prog.runR_eq code]
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self => by
    show TRun.tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
        other.ext other.runR sargs sbody.ext sbody.runR self =
      TRun.tryCall call rets ok.ext ok.runC err.ext err.runC code pnc.ext pnc.runC
        other.ext other.runC sargs sbody.ext sbody.runC self
    rw [Prog.runR_eq ok, Prog.runR_eq err, Prog.runR_eq pnc, Prog.runR_eq other,
      Prog.runR_eq sbody]
  | _, _, .loop a c body => by
    show TRun.loop c body.ext body.runR = TRun.loop c body.ext body.runC
    rw [Prog.runR_eq body]
  | _, _, .block body => by
    show TRun.block body.ext body.runR = TRun.block body.ext body.runC
    rw [Prog.runR_eq body]
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .declLocal ..
  | _, _, .declStorage .. | _, _, .opAssign .. | _, _, .incDec .. | _, _, .assignIncDec ..
  | _, _, .pushOpAssign .. | _, _, .pushIncDec ..
  | _, _, .assignLocalPush .. | _, _, .push .. | _, _, .pop .. | _, _, .transfer ..
  | _, _, .send .. | _, _, .declMem ..
  | _, _, .rebindMem .. | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete ..
  | _, _, .deleteMem .. | _, _, .assignNew .. | _, _, .require .. | _, _, .assert ..
  | _, _, .revert | _, _, .assumeFalse => rfl

theorem Prog.runR_eq : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.runR P = Prog.runC P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    show TRun.seq s.runR P.runR = TRun.seq s.runC P.runC
    rw [Stmt.runR_eq s, Prog.runR_eq P]

end

/-! ### Equations -/

section Equations

variable {Γ : Ctx}

/-- How a typed result halts, if it does. -/
def TRes.halt? {α : Type} : TRes α → Option THalt
  | .ok _ => none
  | .error h => some h

theorem Prog.run_nil (σ : State C Γ) :
    Prog.run σ (.nil : Prog C Γ Γ) = .ok ⟨σ, List.prefix_refl _⟩ := rfl

/-- A sequence whose first statement runs to `o` runs the rest from `o`'s
state. -/
theorem Prog.run_cons_ok {Γ₁ Γ₂ : Ctx} {σ : State C Γ} {o : Out C σ.H Γ₁} {s : Stmt C Γ Γ₁}
    {P : Prog C Γ₁ Γ₂} (h : s.run σ = .ok o) :
    Prog.run σ (.cons s P) = (Prog.run o.st P).map fun o' => ⟨o'.st, o.ext.trans o'.ext⟩ := by
  show TRun.seq s.runR P.runR σ = _
  simp only [TRun.seq, Stmt.run] at h ⊢
  rw [h]

/-- **A recursive call runs as the call of its body** (`Stmt.callRec`). -/
theorem Stmt.run_callRec {Γ' ps rs : Ctx} (σ : State C Γ) (f : Name) (d : Nat)
    (args : Args C Γ ps) (ret : CallRet Γ rs Γ') (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) :
    Stmt.run σ (.callRec f d args ret body) = Stmt.run σ (.call f args ret (body ())) := rfl

theorem Stmt.run_loop {Γ₁ : Ctx} (σ : State C Γ) (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) :
    Stmt.run σ (.loop a c body) =
      TLoop.run (fun o : Out C σ.H Γ => (Prog.run o.st body).map
          fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
        (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩ := rfl

end Equations

/-! ## Examples

Scoped programs run on typed states: the storage the contract deploys with,
no memory, no locals. -/

section Examples

def guardLowCore := sol[StandardExample]{ require(age > 3); }
def assertLowCore := sol[StandardExample]{ assert(age > 3); }
def incOrderCore := sol[TestSuite]{ uint i = 1; uint x = i++ + i; assert(x == 2); assert(i == 2); }
def indexOrderCore := sol[TestSuite]{ uint i = 0; values.push(100);
  values.push(100); values.push(100); values[++i] = ++i; assert(values[2] == 1); }

/-- A failing guard reverts. -/
example : (Prog.run (State.ofStorage Storage.standardExample) guardLowCore).halt? =
    some .revert := by
  decide +kernel

/-- A failing assertion panics. -/
example : (Prog.run (State.ofStorage Storage.standardExample) assertLowCore).halt? =
    some .panic := by
  decide +kernel

/-- solc's order of `++` inside an expression. -/
example : (Prog.run (State.ofStorage Storage.testSuite) incOrderCore).halt? = none := by
  decide +kernel

example : (Prog.run (State.ofStorage Storage.testSuite) indexOrderCore).halt? = none := by
  decide +kernel

/-- The calls of `CallsExample`: `addTwo(3)` is `5`, `larger(5, 7)` is `7`. -/
example : (match Prog.run (State.ofStorage (Storage.init CallsExample)) callsCore with
    | .ok o => some ((TEnv.get .here o.st.env : PrimTy.uint.Denote).1,
        (TEnv.get (.there .here) o.st.env : PrimTy.uint.Denote).1)
    | .error _ => none) = some (7, 5) := by
  decide +kernel

end Examples


end Solidity
