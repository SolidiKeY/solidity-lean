import Solidity.Semantics
import Solidity.Syntax.CoreQuote

/-!
# The interpreter over the scoped syntax

`Semantics.lean`'s interpreter for `Syntax/Core.lean`'s programs
(`docs/intrinsic.md`, M3): a state carries the locals of its context
`Γ`, `Env C Γ`, a type computed from `Γ` (`Unit`, then one component per
local, innermost first), so a local is read and written by its position and
never missing nor of another kind.  `Stmt.run σ s : Res (State C Γ')`
leaves the context the statement's type says: a declaration pushes, the end
of a scope (a branch, a loop's iteration, a block, a call's frame, a `try`'s
clause) pops by the suffix `Prog.ext` (`State.drop`).

Until M4 the storage, the heap and the values are `Semantics.lean`'s,
untyped: a value is a `Value`, an alias a storage path, a memory local a heap
identity, and the run calls `Semantics.lean`'s operations on the global part
of the state (`State.glob`).  So `stuck` is still reached, by a value of
another shape than its type (a `bool` where a `uint` is read: M4a) and by a
storage or heap that does not fit (M4b, M4c), never by a local.

Where the kernel evaluates (`rfl` and `decide` on a run, Gate G0): `Env`'s
functions recurse on `Idx`/`Ext` by `casesOn` (condition 1), and `Stmt.run`
and `Prog.run` are `Stmt.rec` with a twin for the compiler (`Stmt.runC`,
condition 2) linked by `Stmt.runR_eq`/`Prog.runR_eq`.  Each statement's step is one
function (`Run.*`) that both call, given its sub-programs' runs.
-/

namespace Solidity.Core

open Semantics (Value SVal MVal Seg Halt Res copyStToM allocDefault copyMem applyBinOp
  applyUnOp checkArith lookupBy)

variable {C : Contract}

/-! ## Locals -/

/-- What a local of type `t` holds: a value, the storage path an alias is
bound to (`none` while unset), a memory object's identity (`none` while
unset: only a hidden binder leaves one so, decision 17'), a whole storage
(`old`) or ledger (`oldNet`).  Reducible, so a local's value finds the instances of its type. -/
@[reducible] def LTy.Denote (_C : Contract) : LTy → Type
  | .val _ => Value
  | .alias _ => Option (Name × List Seg)
  | .mem _ => Option Nat
  | .old => List (Name × SVal)
  | .oldNet => List (Int × Int)

/-- The locals of `Γ`, innermost first: a type computed from `Γ`, not an
inductive family (condition 4). -/
def Env (C : Contract) : Ctx → Type
  | [] => Unit
  | t :: Γ => t.Denote C × Env C Γ

namespace Env

/-- The local at a position. -/
def get : {Γ : Ctx} → {t : LTy} → Idx Γ t → Env C Γ → t.Denote C
  | _, _, i => Idx.casesOn (motive := fun Γ t _ => Env C Γ → t.Denote C) i (fun e => e.1)
      (fun i e => Env.get i e.2)
  termination_by structural _ _ i => i

/-- The local at a position, set. -/
def set : {Γ : Ctx} → {t : LTy} → Idx Γ t → t.Denote C → Env C Γ → Env C Γ
  | _, _, i => Idx.casesOn (motive := fun Γ t _ => t.Denote C → Env C Γ → Env C Γ) i
      (fun w e => (w, e.2)) (fun i w e => (e.1, Env.set i w e.2))
  termination_by structural _ _ i => i

/-- The locals a suffix pushed, popped. -/
def drop {Γ : Ctx} : {Δ : Ctx} → Ext Γ Δ → Env C Δ → Env C Γ
  | _, h => Ext.casesOn (motive := fun Δ _ => Env C Δ → Env C Γ) h (fun e => e)
      (fun h e => Env.drop h e.2)
  termination_by structural _ h => h

/-- The locals `ρ` on top of `Γ`'s. -/
def append {Γ : Ctx} : (ρ : Ctx) → Env C ρ → Env C Γ → Env C (ρ ++ Γ)
  | [], _, e => e
  | _ :: ρ, r, e => (r.1, Env.append ρ r.2 e)

/-- The top `ρ` of the locals. -/
def take {Γ : Ctx} : (ρ : Ctx) → Env C (ρ ++ Γ) → Env C ρ
  | [], _ => ()
  | _ :: ρ, e => (e.1, Env.take ρ e.2)

theorem get_set {Γ : Ctx} {t : LTy} (i : Idx Γ t) (v : t.Denote C) (e : Env C Γ) :
    Env.get i (Env.set i v e) = v := by
  induction i with
  | here => rfl
  | there i ih => exact ih v e.2

theorem take_append {Γ : Ctx} (ρ : Ctx) (r : Env C ρ) (e : Env C Γ) :
    Env.take ρ (Env.append ρ r e) = r := by
  induction ρ with
  | nil => rfl
  | cons t ρ ih => show (r.1, Env.take ρ (Env.append ρ r.2 e)) = r; rw [ih]; rfl

theorem drop_append {Γ : Ctx} (ρ : Ctx) (r : Env C ρ) (e : Env C Γ) :
    Env.drop (Ext.append Γ ρ) (Env.append ρ r e) = e := by
  induction ρ with
  | nil => rfl
  | cons t ρ ih => exact ih r.2

end Env

/-! ## States -/

/-- A state in the context `Γ`: `Semantics.State`'s parts, the locals typed
by `Γ`. -/
structure State (C : Contract) (Γ : Ctx) where
  storage : List (Name × SVal)
  heap : List (Nat × Semantics.MObj) := []
  nextId : Nat := 0
  env : Env C Γ
  net : List (Int × Int) := []
  selfBalance : Int := 0
  tx : Semantics.TxEnv := {}

namespace State

/-- Everything but the locals, as `Semantics.lean`'s operations take it. -/
def glob {Γ : Ctx} (σ : State C Γ) : Semantics.State :=
  { storage := σ.storage, heap := σ.heap, nextId := σ.nextId, net := σ.net,
    selfBalance := σ.selfBalance, tx := σ.tx }

/-- A global part with locals. -/
def ofGlob {Γ : Ctx} (τ : Semantics.State) (e : Env C Γ) : State C Γ :=
  { storage := τ.storage, heap := τ.heap, nextId := τ.nextId, env := e, net := τ.net,
    selfBalance := τ.selfBalance, tx := τ.tx }

/-- The global part replaced. -/
def withGlob {Γ : Ctx} (σ : State C Γ) (τ : Semantics.State) : State C Γ := ofGlob τ σ.env

/-- The locals replaced, in another context. -/
def withEnv {Γ Δ : Ctx} (σ : State C Γ) (e : Env C Δ) : State C Δ :=
  { storage := σ.storage, heap := σ.heap, nextId := σ.nextId, env := e, net := σ.net,
    selfBalance := σ.selfBalance, tx := σ.tx }

/-- A local declared. -/
def push {Γ : Ctx} {t : LTy} (σ : State C Γ) (v : t.Denote C) : State C (t :: Γ) :=
  σ.withEnv (v, σ.env)

/-- A local set. -/
def setLocal {Γ : Ctx} {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.Denote C) : State C Γ :=
  σ.withEnv (Env.set i v σ.env)

/-- A scope's locals popped. -/
def drop {Γ Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) : State C Γ := σ.withEnv (Env.drop h σ.env)

end State

/-! ## Expressions -/

section Eval

variable {Γ : Ctx}

/-- The value a simple value denotes: a literal, a local's, the
environment's. -/
def Simple.eval (σ : State C Γ) {p : PrimTy} : Simple C Γ p → Res Value
  | .lit n _ => pure (.int n)
  | .bool b => pure (.bool b)
  | .local i => pure (Env.get i σ.env)
  | .env k _ => pure (.int (σ.glob.envVal k))

/-- The path an alias is bound to; an unset one reverts. -/
def aliasPath (σ : State C Γ) {R : RefTy} (i : Idx Γ (.alias R)) : Res (Name × List Seg) :=
  match (Env.get i σ.env : Option (Name × List Seg)) with
  | some p => pure p
  | none => .error .revert

/-- The object a memory local names; an unset one reverts, as an unset
alias does (decision 17'). -/
def memRef (σ : State C Γ) {R : RefTy} (i : Idx Γ (.mem R)) : Res Nat :=
  match (Env.get i σ.env : Option Nat) with
  | some id => pure id
  | none => .error .revert

mutual

/-- The storage path a path denotes in `σ`. -/
def SPath.resolve (σ : State C Γ) : {T : Ty} → SPath C Γ T → Res (Name × List Seg)
  | _, .alias i => aliasPath σ i
  | _, .loc l => l.resolve σ

def Loc.resolve (σ : State C Γ) : {T : Ty} → Loc C Γ T → Res (Name × List Seg)
  | _, .root r _ => pure (r, [])
  | _, .field b f _ => do
    let (r, segs) ← b.resolve σ
    pure (r, segs ++ [.field f])
  | _, .index (k := k) _ b i => do
    let (r, segs) ← b.resolve σ
    let i ← (← i.eval σ).keyAt k
    σ.glob.checkIndex r segs i
    pure (r, segs ++ [.at i])

/-- The slot a memory path holds in `σ`. -/
def MPath.mval (σ : State C Γ) : {T : Ty} → MPath C Γ T → Res MVal
  | _, .var i _ => do pure (.ref (← memRef σ i))
  | _, .loc l => l.read σ

def MLoc.read (σ : State C Γ) : {T : Ty} → MLoc C Γ T → Res MVal
  | _, .field b f _ => do
    let id ← (← b.mval σ).asRef
    match ← σ.glob.getObj id with
    | .struct fields =>
      match lookupBy f fields with
      | some v => pure v
      | none => .error .stuck
    | .array _ _ => .error .stuck
  | _, .index _ b i => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    match ← σ.glob.getObj id with
    | .array elems _ =>
      if h : 0 ≤ iv ∧ iv.toNat < elems.length then pure (elems.get ⟨iv.toNat, h.2⟩)
      else .error .revert
    | .struct _ => .error .stuck

/-- The value a value expression denotes in `σ`. -/
def Val.eval (σ : State C Γ) : {p : PrimTy} → Val C Γ p → Res Value
  | _, .simple s => s.eval σ
  | _, .read l => do
    let (r, segs) ← l.resolve σ
    (← σ.glob.findStorage r segs).asValue
  | _, @Val.binop _ _ p _ op _ _ a b => do evalBinop op p (← a.eval σ) (b.eval σ)
  | _, @Val.unop _ _ p _ op _ _ a => do unopCheck op p (← applyUnOp op (← a.eval σ))
  | _, .ternary c a b => do pickBranch (← c.eval σ) (a.eval σ) (b.eval σ)
  | _, .readMem l => do (← l.read σ).asValue
  | _, .len b _ => do
    let (r, segs) ← b.resolve σ
    arrayLen σ.glob r segs
  | _, .mlen b _ => do memArrayLen σ.glob (← (← b.mval σ).asRef)

end

/-- The storage value a source stores. -/
def Src.value (σ : State C Γ) {T : Ty} : Src C Γ T → Res SVal
  | .val v => do pure (← v.eval σ).toSVal
  | .copy p _ => do
    let (r, segs) ← p.resolve σ
    σ.glob.findStorage r segs

/-- What a push appends: the slot, or its argument laid on fresh slots. -/
def Src.pushVal (σ : State C Γ) {T : Ty} : Option (Src C Γ T) → SVal → Res SVal
  | none, slot => pure slot
  | some r, _ => do pure (← r.value σ).strip

/-- `l = mv` into a memory location. -/
def MLoc.write (σ : State C Γ) (mv : MVal) {T : Ty} : MLoc C Γ T → Res (State C Γ)
  | .field b f _ => do
    let id ← (← b.mval σ).asRef
    σ.withGlob <$> memWriteField σ.glob id f mv
  | .index _ b i => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    σ.withGlob <$> memWriteIndex σ.glob id iv mv

/-- The slot a memory source writes. -/
def MSrc.mval (σ : State C Γ) {T : Ty} : MSrc C Γ T → Res MVal
  | .val v => do pure (← v.eval σ).toMVal
  | .ref p => do pure (.ref (← (← p.mval σ).asRef))

/-- The object a memory right-hand side names, and the state its
allocation leaves: an object by identity, a deep copy, a fresh array. -/
def MRhs.eval (σ : State C Γ) {R : RefTy} : MRhs C Γ R → Res (State C Γ × Nat)
  | .alias p => do pure (σ, ← (← p.mval σ).asRef)
  | .copy p _ => do
    let (root, segs) ← p.resolve σ
    let sv ← σ.glob.findStorage root segs
    let (τ, mv) ← copyStToM σ.glob sv
    pure (σ.withGlob τ, ← mv.asRef)
  | .newArr n _ => do
    let sv := newArrVal R (← (← n.eval σ).asInt)
    let (τ, mv) ← copyStToM σ.glob sv
    pure (σ.withGlob τ, ← mv.asRef)

/-- The path an alias's right-hand side names, and the state a push leaves. -/
def ARhs.eval (σ : State C Γ) {R : RefTy} : ARhs C Γ R → Res (State C Γ × (Name × List Seg))
  | .path p => do pure (σ, ← p.resolve σ)
  | .push b _ => do
    let (root, segs) ← b.resolve σ
    let (τ, n) ← pushPlaceAt σ.glob (.ref R) root segs
    pure (σ.withGlob τ, (root, segs ++ [.at n]))

/-- The address of a memory location. -/
def MLoc.addr (σ : State C Γ) {T : Ty} : MLoc C Γ T → Res Semantics.Addr
  | .field b f _ => do pure (.memoryField (← (← b.mval σ).asRef) f)
  | .index _ b i => do
    let id ← (← b.mval σ).asRef
    pure (.memoryIndex id (← (← i.eval σ).asInt))

/-- A memory write is a write at its location's address. -/
theorem MLoc.write_eq (σ : State C Γ) (mv : MVal) {T : Ty} (l : MLoc C Γ T) :
    l.write σ mv = l.addr σ >>= fun a => σ.withGlob <$> Solidity.writeAddr σ.glob mv a := by
  cases l <;> simp only [MLoc.write, MLoc.addr, Solidity.writeAddr, bind_assoc, pure_bind]

/-- `x ⊕= v` on a local. -/
def opLocal (σ : State C Γ) (op : BinOp) (p : PrimTy) (i : Idx Γ (.val p)) (v : Value) :
    Res (State C Γ) := do
  let new ← applyBinOp op (Env.get i σ.env) v
  let new ← checkArith (.prim p) new
  pure (σ.setLocal i new)

/-- A compound assignment's write of `v` into its target. -/
def OpLoc.store (σ : State C Γ) (op : BinOp) : {p : PrimTy} → OpLoc C Γ p → Value →
    Res (State C Γ)
  | p, .local i, v => opLocal σ op p i v
  | p, .root r _, v => σ.withGlob <$> opStore σ.glob op p r [] v
  | p, .field b f h, v => do
    let (rt, segs) ← (Loc.field b f h).resolve σ
    σ.withGlob <$> opStore σ.glob op p rt segs v
  | p, .index it b i, v => do
    let (rt, segs) ← (Loc.index it b (.simple i)).resolve σ
    σ.withGlob <$> opStore σ.glob op p rt segs v
  | p, .mfield b f _, v => do
    let id ← (← b.mval σ).asRef
    σ.withGlob <$> opMem σ.glob op p (.memoryField id f) v
  | p, .mindex _ b i, v => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    σ.withGlob <$> opMem σ.glob op p (.memoryIndex id iv) v

/-- `x++` on a local: the state, and the value. -/
def bumpLocal (σ : State C Γ) (op : IncDec) (p : PrimTy) (i : Idx Γ (.val p)) :
    Res (State C Γ × Value) := do
  let old : Value := Env.get i σ.env
  let oldInt ← old.asInt
  let new ← checkArith (.prim p) (.int (if op.isIncrement then oldInt + 1 else oldInt - 1))
  pure (σ.setLocal i new, if op.isPre then new else old)

/-- A global step's state and value, with the locals. -/
private def withGlob₂ (σ : State C Γ) : Semantics.State × Value → State C Γ × Value
  | (τ, v) => (σ.withGlob τ, v)

/-- `l++`: the state it leaves, and its value. -/
def OpLoc.bump (σ : State C Γ) (op : IncDec) : {p : PrimTy} → OpLoc C Γ p →
    Res (State C Γ × Value)
  | p, .local i => bumpLocal σ op p i
  | p, .root r _ => withGlob₂ σ <$> bumpStore σ.glob op p r []
  | p, .field b f h => do
    let (rt, segs) ← (Loc.field b f h).resolve σ
    withGlob₂ σ <$> bumpStore σ.glob op p rt segs
  | p, .index it b i => do
    let (rt, segs) ← (Loc.index it b (.simple i)).resolve σ
    withGlob₂ σ <$> bumpStore σ.glob op p rt segs
  | p, .mfield b f _ => do
    let id ← (← b.mval σ).asRef
    withGlob₂ σ <$> bumpMem σ.glob op p (.memoryField id f)
  | p, .mindex _ b i => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    withGlob₂ σ <$> bumpMem σ.glob op p (.memoryIndex id iv)

/-- `pv = a.send(v);` with both evaluated (`Solidity.sendAt`). -/
def sendAt (σ : State C Γ) (pv : Idx Γ (.val .bool)) (addr amt : Int) : Res (State C Γ) :=
  if amt < 0 then .error .revert
  else match lookupBy (sendKey addr amt) σ.tx.ext with
    | none | some (.ok _) => .ok ((σ.withGlob (σ.glob.pay addr amt)).setLocal pv (.bool true))
    | some _ => .ok (σ.setLocal pv (.bool false))

/-- The call as it is made, its receiver and arguments evaluated. -/
def ExtCall.key (σ : State C Γ) (c : ExtCall C Γ) : Res Semantics.ExtKey := do
  let a ← (← c.addr.eval σ).asInt
  let vs ← c.args.mapM fun a => a.2.eval σ
  pure ⟨a, c.fn, vs⟩

/-- A call's arguments, each read in the caller's state, in order. -/
def Args.eval (σ : State C Γ) : {ps : Ctx} → Args C Γ ps → Res (Env C ps)
  | _, as => Args.casesOn (motive := fun ps _ => Res (Env C ps)) as (pure ())
      (fun as _ _ e => do
        let r ← Args.eval σ as
        let v ← e.eval σ
        pure (v, r))
  termination_by structural _ as => as

end Eval

/-- The return variables at their defaults. -/
def Binders.defaults : {ρ : Ctx} → Binders ρ → Env C ρ
  | _, bs => Binders.casesOn (motive := fun ρ _ => Env C ρ) bs ()
      (fun bs p _ => (PrimTy.default p, Binders.defaults bs))
  termination_by structural _ bs => bs

/-- The locals an external call's data binds, in order, and the data left:
too short, or a word not of its local's type, reverts (`bindData`). -/
def Binders.decode : {ρ : Ctx} → Binders ρ → List Value → Res (Env C ρ × List Value)
  | _, bs => Binders.casesOn (motive := fun ρ _ => List Value → Res (Env C ρ × List Value)) bs
      (fun vs => pure ((), vs))
      (fun bs p _ vs => do
        let (e, rest) ← Binders.decode bs vs
        match rest with
        | v :: rest => if v.fits p then pure ((v, e), rest) else .error .revert
        | [] => .error .revert)
  termination_by structural _ bs => bs

/-- The `Panic` code bound, if the clause names it. -/
def CodeBinder.decode {κ : Ctx} (code : CodeBinder κ) (c : Value) : Res (Env C κ) :=
  CodeBinder.casesOn (motive := fun κ _ => Res (Env C κ)) code (pure ())
    (fun _ => if c.fits .uint then pure (c, ()) else .error .revert)

/-- Entering a call: its return variables at their defaults (a memory return
a fresh default object), on the global part `τ`. -/
def CallRet.enter {Γ : Ctx} (τ : Semantics.State) {rs Γ' : Ctx} (ret : CallRet Γ rs Γ') :
    Res (Semantics.State × Env C rs) :=
  CallRet.casesOn (motive := fun rs _ _ => Res (Semantics.State × Env C rs)) ret
    (pure (τ, ()))
    (fun p _ _ => pure (τ, (PrimTy.default p, ())))
    (fun bs => pure (τ, Binders.defaults bs))
    (fun R _ _ _ => do
      let (τ', id) ← allocDefault τ R
      pure (τ', (some id, ())))

/-- Leaving a call: the caller's locals `e`, with what the call leaves them
from its return variables `r`. -/
def CallRet.leave {Γ : Ctx} (e : Env C Γ) {rs Γ' : Ctx} (ret : CallRet Γ rs Γ') :
    Env C rs → Env C Γ' :=
  CallRet.casesOn (motive := fun rs Γ' _ => Env C rs → Env C Γ') ret
    (fun _ => e)
    (fun _ _ res r => match res with
      | .some i => Env.set i r.1 e
      | .none => e)
    (fun {rs} _ r => Env.append rs r e)
    (fun _ _ _ _ r => (r.1, e))

/-- A condition's outcome: `true` goes on, `false` reverts. -/
def guardOk {α : Type} (v : Value) (a : α) : Res α :=
  match v with
  | .bool true => pure a
  | .bool false => .error .revert
  | .int _ => .error .stuck

/-- An assertion's outcome: `true` goes on, `false` panics. -/
def assertOk {α : Type} (v : Value) (a : α) : Res α :=
  match v with
  | .bool true => pure a
  | .bool false => .error .panic
  | .int _ => .error .stuck

/-! ## Loops

`Semantics.lean`'s least fixed point of the unwinding, over any state type
(here `State C Γ`, the body's locals popped each iteration). -/

namespace Loop

variable {α : Type}

def step (body : α → Res α) (c : α → Res Value) (σ : α) : α ⊕ Res α :=
  match c σ with
  | .error h => .inr (.error h)
  | .ok (.bool false) => .inr (.ok σ)
  | .ok (.bool true) =>
    match body σ with
    | .error h => .inr (.error h)
    | .ok τ => .inl τ
  | .ok (.int _) => .inr (.error .stuck)

def iterN (body : α → Res α) (c : α → Res Value) : Nat → α → α ⊕ Res α
  | 0, σ => .inl σ
  | n + 1, σ =>
    match step body c σ with
    | .inl τ => iterN body c n τ
    | .inr r => .inr r

partial def runImpl [Inhabited α] (body : α → Res α) (c : α → Res Value) (σ : α) : Res α :=
  match step body c σ with
  | .inl τ => runImpl body c τ
  | .inr r => r

/-- The compiled loop, for a state type with no `Inhabited` instance. -/
def runImpl' (body : α → Res α) (c : α → Res Value) (σ : α) : Res α :=
  @runImpl α ⟨σ⟩ body c σ

open Classical in
/-- The loop's outcome, or `diverge` when no iteration is done. -/
@[implemented_by runImpl']
noncomputable def run (body : α → Res α) (c : α → Res Value) (σ : α) : Res α :=
  if h : ∃ r n, iterN body c n σ = .inr r then Classical.choose h else .error .diverge

theorem iterN_done_le {body : α → Res α} {c : α → Res Value} {n m : Nat} {σ : α} {r : Res α}
    (hnm : n ≤ m) (h : iterN body c n σ = .inr r) : iterN body c m σ = .inr r := by
  induction n generalizing σ m with
  | zero => simp only [iterN, reduceCtorEq] at h
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [iterN] at h ⊢
    cases hs : step body c σ with
    | inl τ => rw [hs] at h; exact ih (by omega) h
    | inr r' => rw [hs] at h; exact h

theorem iterN_done_unique {body : α → Res α} {c : α → Res Value} {n m : Nat} {σ : α}
    {r r' : Res α} (h : iterN body c n σ = .inr r) (h' : iterN body c m σ = .inr r') :
    r = r' := by
  rcases Nat.le_total n m with hnm | hmn
  · rw [iterN_done_le hnm h] at h'
    exact Sum.inr.inj h'
  · rw [iterN_done_le hmn h'] at h
    exact (Sum.inr.inj h).symm

/-- A loop done at `n` ends as it is done there. -/
theorem run_of_iterN {body : α → Res α} {c : α → Res Value} {n : Nat} {σ : α} {r : Res α}
    (h : iterN body c n σ = .inr r) : run body c σ = r := by
  have hex : ∃ r n, iterN body c n σ = .inr r := ⟨r, n, h⟩
  simp only [run, hex, dite_true]
  obtain ⟨n', h'⟩ := Classical.choose_spec hex
  exact iterN_done_unique h' h

end Loop

/-! ## Statements

One function per statement, given the runs of its sub-programs and the
suffixes they push. -/

namespace Run

variable {Γ : Ctx}

def assign {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) (σ : State C Γ) : Res (State C Γ) := do
  let sv ← r.value σ
  let (root, segs) ← l.resolve σ
  σ.withGlob <$> σ.glob.writeStorage root segs sv

def rebind {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) (σ : State C Γ) :
    Res (State C Γ) := do
  let (σ', p) ← r.eval σ
  pure (σ'.setLocal i (some p))

def assignLocal {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) (σ : State C Γ) :
    Res (State C Γ) := do
  pure (σ.setLocal i (← r.eval σ))

def declLocal (p : PrimTy) (init : Option (Val C Γ p)) (σ : State C Γ) :
    Res (State C (.val p :: Γ)) := do
  let v ← match init with
    | none => pure (PrimTy.default p)
    | some e => e.eval σ
  pure (σ.push (t := .val p) v)

def declStorage (R : RefTy) (init : Option (ARhs C Γ R)) (σ : State C Γ) :
    Res (State C (.alias R :: Γ)) :=
  match init with
  | none => pure (σ.push (t := .alias R) none)
  | some r => do
    let (σ', p) ← r.eval σ
    pure (σ'.push (t := .alias R) (some p))

def opAssign {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (r : Val C Γ p) (σ : State C Γ) :
    Res (State C Γ) := do
  l.store σ op (← r.eval σ)

def incDec {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) (σ : State C Γ) : Res (State C Γ) := do
  pure (← l.bump σ op).1

def assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (l : OpLoc C Γ p)
    (σ : State C Γ) : Res (State C Γ) := do
  let (σ', v) ← l.bump σ op
  pure (σ'.setLocal i v)

def push {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) (σ : State C Γ) :
    Res (State C Γ) := do
  let (root, segs) ← b.resolve σ
  σ.withGlob <$> pushAt σ.glob E root segs (Src.pushVal σ v)

def pop {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ) : Res (State C Γ) := do
  let (root, segs) ← b.resolve σ
  σ.withGlob <$> popAt σ.glob E.isMapping root segs

def transfer (r a : Val C Γ .uint) (σ : State C Γ) : Res (State C Γ) := do
  let addr ← (← r.eval σ).asInt
  let amt ← (← a.eval σ).asInt
  σ.withGlob <$> transferAt σ.glob addr amt

def send (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (σ : State C Γ) :
    Res (State C Γ) := do
  let addr ← (← r.eval σ).asInt
  let amt ← (← a.eval σ).asInt
  sendAt σ pv addr amt

def declMem (R : RefTy) (init : Option (MRhs C Γ R)) (σ : State C Γ) :
    Res (State C (.mem R :: Γ)) :=
  match init with
  | none => do
    let (τ, id) ← allocDefault σ.glob R
    pure ((σ.withGlob τ).push (t := .mem R) (some id))
  | some r => do
    let (σ', id) ← r.eval σ
    pure (σ'.push (t := .mem R) (some id))

def rebindMem {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (σ : State C Γ) :
    Res (State C Γ) := do
  let (σ', id) ← r.eval σ
  pure (σ'.setLocal i (some id))

def assignFromMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) (σ : State C Γ) :
    Res (State C Γ) := do
  let sv ← copyMem σ.glob (.ref (← (← p.mval σ).asRef))
  let (root, segs) ← l.resolve σ
  σ.withGlob <$> σ.glob.writeStorage root segs sv

def assignMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) (σ : State C Γ) : Res (State C Γ) := do
  l.write σ (← r.mval σ)

def delete {T : Ty} (l : Loc C Γ T) (σ : State C Γ) : Res (State C Γ) := do
  let (root, segs) ← l.resolve σ
  let cur ← σ.glob.findStorage root segs
  σ.withGlob <$> σ.glob.saveStorage root segs cur.defaultOf

def deleteMem {T : Ty} (p : MPath C Γ T) (σ : State C Γ) : Res (State C Γ) :=
  match p with
  | @MPath.var _ _ R i _ => do
    let (τ, id) ← allocDefault σ.glob R
    pure ((σ.withGlob τ).setLocal i (some id))
  | .loc l => do σ.withGlob <$> memClear σ.glob (← l.addr σ) T

def assignNew {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint) (σ : State C Γ) :
    Res (State C Γ) := do
  let sv := newArrVal R (← (← n.eval σ).asInt)
  let (τ, mv) ← copyStToM σ.glob sv
  let id ← mv.asRef
  let σ' := σ.withGlob τ
  match l with
  | .store l => do
    let sv' ← copyMem τ (.ref id)
    let (root, segs) ← l.resolve σ'
    σ'.withGlob <$> τ.writeStorage root segs sv'
  | .mem l => l.write σ' (.ref id)

/-- `if`: the branch the condition picks, its locals popped. -/
def ite {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) (thn : State C Γ → Res (State C Γ₁))
    (h₂ : Ext Γ Γ₂) (els : State C Γ → Res (State C Γ₂)) (σ : State C Γ) : Res (State C Γ) := do
  match ← c.eval σ with
  | .bool true => (thn σ).map (State.drop h₁)
  | .bool false => (els σ).map (State.drop h₂)
  | .int _ => .error .stuck

/-- A call: the arguments read, the frame entered (parameters, then return
variables), the body run in it, and what the call leaves the caller. -/
def call {Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) (body : State C (rs ++ ps) → Res (State C Γf)) (σ : State C Γ) :
    Res (State C Γ') := do
  let a ← args.eval σ
  let (τ, r) ← ret.enter σ.glob
  let υ ← body (State.ofGlob τ (Env.append rs r a))
  pure (υ.withEnv (ret.leave σ.env (Env.take rs (Env.drop hb υ.env))))

/-- `try`: the clause the transaction's outcome picks, its locals popped. -/
def tryCall {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : State C (ρ ++ Γ) → Res (State C Γ₁))
    (h₂ : Ext Γ Γ₂) (err : State C Γ → Res (State C Γ₂)) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : State C (κ ++ Γ) → Res (State C Γ₃))
    (h₄ : Ext Γ Γ₄) (other : State C Γ → Res (State C Γ₄)) (σ : State C Γ) :
    Res (State C Γ) := do
  match lookupBy (← call.key σ) σ.tx.ext with
  | none => .error .revert
  | some (.ok vs) => do
    let (r, _) ← rets.decode vs
    (ok (σ.withEnv (Env.append ρ r σ.env))).map (State.drop ((Ext.append Γ ρ).trans h₁))
  | some .error => (err σ).map (State.drop h₂)
  | some (.panic c) => do
    let r ← code.decode c
    (pnc (σ.withEnv (Env.append κ r σ.env))).map (State.drop ((Ext.append Γ κ).trans h₃))
  | some .other => (other σ).map (State.drop h₄)

/-- `while`: the body's locals popped every iteration. -/
def loop {Γ₁ : Ctx} (c : Val C Γ .bool) (h : Ext Γ Γ₁)
    (body : State C Γ → Res (State C Γ₁)) (σ : State C Γ) : Res (State C Γ) :=
  Loop.run (fun τ => (body τ).map (State.drop h)) (fun τ => c.eval τ) σ

/-- A block: its locals popped. -/
def block {Γ₁ : Ctx} (h : Ext Γ Γ₁) (body : State C Γ → Res (State C Γ₁)) (σ : State C Γ) :
    Res (State C Γ) :=
  (body σ).map (State.drop h)

/-- A sequence: the first statement, then the rest. -/
def seq {Γ₁ Γ₂ : Ctx} (s : State C Γ → Res (State C Γ₁)) (P : State C Γ₁ → Res (State C Γ₂))
    (σ : State C Γ) : Res (State C Γ₂) :=
  match s σ with
  | .ok τ => P τ
  | .error e => .error e

end Run

/-! ## Running a program

`Stmt.runC` is the compiler's: structural, by `match`.  `Stmt.run` is the
kernel's: the recursor, with the same steps (`Run.*`), so evaluating a run
unfolds no `brecOn` and casts no index (Gate G0, conditions 1 and 2). -/

mutual

/-- The compiled run of a statement. -/
def Stmt.runC : {Γ Γ' : Ctx} → Stmt C Γ Γ' → State C Γ → Res (State C Γ')
  | _, _, .assign l r => Run.assign l r
  | _, _, .rebind i r => Run.rebind i r
  | _, _, .assignLocal i r => Run.assignLocal i r
  | _, _, .declLocal p _ init => Run.declLocal p init
  | _, _, .declStorage R _ init => Run.declStorage R init
  | _, _, .opAssign op _ _ l r => Run.opAssign op l r
  | _, _, .incDec op _ l => Run.incDec op l
  | _, _, .assignIncDec i op _ l _ => Run.assignIncDec i op l
  | _, _, .push b v _ => Run.push b v
  | _, _, .pop b => Run.pop b
  | _, _, .transfer r a => Run.transfer r a
  | _, _, .send pv r a => Run.send pv r a
  | _, _, .declMem R _ init _ _ => Run.declMem R init
  | _, _, .rebindMem i r => Run.rebindMem i r
  | _, _, .assignFromMem l p => Run.assignFromMem l p
  | _, _, .assignMem l r => Run.assignMem l r
  | _, _, .delete l => Run.delete l
  | _, _, .deleteMem p _ => Run.deleteMem p
  | _, _, .assignNew l n _ => Run.assignNew l n
  | _, _, .ite c thn els => Run.ite c thn.ext (Prog.runC thn) els.ext (Prog.runC els)
  | _, _, .require c => fun σ => do guardOk (← c.eval σ) σ
  | _, _, .assert c => fun σ => do assertOk (← c.eval σ) σ
  | _, _, .revert => fun _ => .error .revert
  | _, _, .call _ args ret body => Run.call args ret body.ext (Prog.runC body)
  | _, _, .tryCall call rets ok err code pnc other =>
    Run.tryCall call rets ok.ext (Prog.runC ok) err.ext (Prog.runC err) code pnc.ext
      (Prog.runC pnc) other.ext (Prog.runC other)
  | _, _, .loop _ c body => Run.loop c body.ext (Prog.runC body)
  | _, _, .block body => Run.block body.ext (Prog.runC body)

/-- The compiled run of a sequence. -/
def Prog.runC : {Γ Γ' : Ctx} → Prog C Γ Γ' → State C Γ → Res (State C Γ')
  | _, _, .nil => pure
  | _, _, .cons s P => Run.seq (Stmt.runC s) (Prog.runC P)

end

/-- The kernel's run of a statement and of a sequence, by their recursor. -/
abbrev runMotive (C : Contract) (Γ Γ' : Ctx) : Type := State C Γ → Res (State C Γ')

/-- The run of a statement: the state it leaves, from `σ`, or how it halts. -/
@[implemented_by Stmt.runC]
def Stmt.runR {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : State C Γ → Res (State C Γ') :=
  Stmt.rec (motive_1 := fun Γ Γ' _ => runMotive C Γ Γ') (motive_2 := fun Γ Γ' _ => runMotive C Γ Γ')
    (fun l r => Run.assign l r) (fun i r => Run.rebind i r) (fun i r => Run.assignLocal i r)
    (fun p _ init => Run.declLocal p init) (fun R _ init => Run.declStorage R init)
    (fun op _ _ l r => Run.opAssign op l r) (fun op _ l => Run.incDec op l)
    (fun i op _ l _ => Run.assignIncDec i op l) (fun b v _ => Run.push b v) (fun b => Run.pop b)
    (fun r a => Run.transfer r a) (fun pv r a => Run.send pv r a)
    (fun R _ init _ _ => Run.declMem R init) (fun i r => Run.rebindMem i r)
    (fun l p => Run.assignFromMem l p) (fun l r => Run.assignMem l r) (fun l => Run.delete l)
    (fun p _ => Run.deleteMem p) (fun l n _ => Run.assignNew l n)
    (fun c thn els ihThn ihEls => Run.ite c thn.ext ihThn els.ext ihEls)
    (fun c σ => do guardOk (← c.eval σ) σ) (fun c σ => do assertOk (← c.eval σ) σ)
    (fun _ => .error .revert)
    (fun _ args ret body ih => Run.call args ret body.ext ih)
    (fun call rets ok err code pnc other ihOk ihErr ihPnc ihOther =>
      Run.tryCall call rets ok.ext ihOk err.ext ihErr code pnc.ext ihPnc other.ext ihOther)
    (fun _ c body ih => Run.loop c body.ext ih) (fun body ih => Run.block body.ext ih)
    pure (fun _ _ ihS ihP => Run.seq ihS ihP) s

/-- The run of a sequence. -/
@[implemented_by Prog.runC]
def Prog.runR {Γ Γ' : Ctx} (P : Prog C Γ Γ') : State C Γ → Res (State C Γ') :=
  Prog.rec (motive_1 := fun Γ Γ' _ => runMotive C Γ Γ') (motive_2 := fun Γ Γ' _ => runMotive C Γ Γ')
    (fun l r => Run.assign l r) (fun i r => Run.rebind i r) (fun i r => Run.assignLocal i r)
    (fun p _ init => Run.declLocal p init) (fun R _ init => Run.declStorage R init)
    (fun op _ _ l r => Run.opAssign op l r) (fun op _ l => Run.incDec op l)
    (fun i op _ l _ => Run.assignIncDec i op l) (fun b v _ => Run.push b v) (fun b => Run.pop b)
    (fun r a => Run.transfer r a) (fun pv r a => Run.send pv r a)
    (fun R _ init _ _ => Run.declMem R init) (fun i r => Run.rebindMem i r)
    (fun l p => Run.assignFromMem l p) (fun l r => Run.assignMem l r) (fun l => Run.delete l)
    (fun p _ => Run.deleteMem p) (fun l n _ => Run.assignNew l n)
    (fun c thn els ihThn ihEls => Run.ite c thn.ext ihThn els.ext ihEls)
    (fun c σ => do guardOk (← c.eval σ) σ) (fun c σ => do assertOk (← c.eval σ) σ)
    (fun _ => .error .revert)
    (fun _ args ret body ih => Run.call args ret body.ext ih)
    (fun call rets ok err code pnc other ihOk ihErr ihPnc ihOther =>
      Run.tryCall call rets ok.ext ihOk err.ext ihErr code pnc.ext ihPnc other.ext ihOther)
    (fun _ c body ih => Run.loop c body.ext ih) (fun body ih => Run.block body.ext ih)
    pure (fun _ _ ihS ihP => Run.seq ihS ihP) P

/-- The state a statement leaves, from `σ`. -/
abbrev Stmt.run {Γ Γ' : Ctx} (σ : State C Γ) (s : Stmt C Γ Γ') : Res (State C Γ') := s.runR σ

/-- The state a sequence leaves, from `σ`. -/
abbrev Prog.run {Γ Γ' : Ctx} (σ : State C Γ) (P : Prog C Γ Γ') : Res (State C Γ') := P.runR σ

/-! ### The two runs agree -/

mutual

theorem Stmt.runR_eq : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → Stmt.runR s = Stmt.runC s
  | _, _, .ite c thn els => by
    show Run.ite c thn.ext thn.runR els.ext els.runR = Run.ite c thn.ext thn.runC els.ext els.runC
    rw [Prog.runR_eq thn, Prog.runR_eq els]
  | _, _, .call f args ret body => by
    show Run.call args ret body.ext body.runR = Run.call args ret body.ext body.runC
    rw [Prog.runR_eq body]
  | _, _, .tryCall call rets ok err code pnc other => by
    show Run.tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR other.ext
        other.runR =
      Run.tryCall call rets ok.ext ok.runC err.ext err.runC code pnc.ext pnc.runC other.ext
        other.runC
    rw [Prog.runR_eq ok, Prog.runR_eq err, Prog.runR_eq pnc, Prog.runR_eq other]
  | _, _, .loop a c body => by
    show Run.loop c body.ext body.runR = Run.loop c body.ext body.runC
    rw [Prog.runR_eq body]
  | _, _, .block body => by
    show Run.block body.ext body.runR = Run.block body.ext body.runC
    rw [Prog.runR_eq body]
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .declLocal ..
  | _, _, .declStorage .. | _, _, .opAssign .. | _, _, .incDec .. | _, _, .assignIncDec ..
  | _, _, .push .. | _, _, .pop .. | _, _, .transfer .. | _, _, .send .. | _, _, .declMem ..
  | _, _, .rebindMem .. | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete ..
  | _, _, .deleteMem .. | _, _, .assignNew .. | _, _, .require .. | _, _, .assert ..
  | _, _, .revert => rfl

theorem Prog.runR_eq : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.runR P = Prog.runC P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    show Run.seq s.runR P.runR = Run.seq s.runC P.runC
    rw [Stmt.runR_eq s, Prog.runR_eq P]

end

/-! ### One equation per scope -/

section Equations

variable {Γ : Ctx}

theorem Prog.run_nil (σ : State C Γ) : Prog.run σ (.nil : Prog C Γ Γ) = .ok σ := rfl

theorem Prog.run_cons {Γ₁ Γ₂ : Ctx} (σ : State C Γ) (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) :
    Prog.run σ (.cons s P) = (s.run σ).bind (Prog.run · P) := by
  show Run.seq s.runR P.runR σ = _
  simp only [Run.seq, Stmt.run]
  cases s.runR σ <;> rfl

/-- A sequence whose first statement runs to `τ` runs the rest from `τ`. -/
theorem Prog.run_cons_ok {Γ₁ Γ₂ : Ctx} {σ : State C Γ} {τ : State C Γ₁} {s : Stmt C Γ Γ₁}
    {P : Prog C Γ₁ Γ₂} (h : s.run σ = .ok τ) : Prog.run σ (.cons s P) = Prog.run τ P := by
  rw [Prog.run_cons, h]; rfl

theorem Stmt.run_ite {Γ₁ Γ₂ : Ctx} (σ : State C Γ) (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) :
    Stmt.run σ (.ite c thn els) = Run.ite c thn.ext thn.runR els.ext els.runR σ := rfl

theorem Stmt.run_block {Γ₁ : Ctx} (σ : State C Γ) (body : Prog C Γ Γ₁) :
    Stmt.run σ (.block body) = (Prog.run σ body).map (State.drop body.ext) := rfl

theorem Stmt.run_loop {Γ₁ : Ctx} (σ : State C Γ) (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) :
    Stmt.run σ (.loop a c body) =
      Loop.run (fun τ => (Prog.run τ body).map (State.drop body.ext)) (fun τ => c.eval τ) σ :=
  rfl

/-- **A concrete loop, run**: done at its `n`-th iteration with `r`, the loop
and the rest of its sequence run as `r` and the rest (`n` found by `#eval`,
the iteration then computed by `rfl`). -/
theorem Prog.run_loop_of_iterN {Γ₁ Γ₂ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Γ₁} {P : Prog C Γ Γ₂} {n : Nat} {r : Res (State C Γ)}
    (h : Loop.iterN (fun τ => (Prog.run τ body).map (State.drop body.ext)) (fun τ => c.eval τ) n σ =
      .inr r) :
    Prog.run σ (.cons (.loop a c body) P) = r.bind (Prog.run · P) := by
  rw [Prog.run_cons, Stmt.run_loop, Loop.run_of_iterN h]

theorem Stmt.run_call {Γ' ps rs Γf : Ctx} (σ : State C Γ) (f : Name) (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) :
    Stmt.run σ (.call f args ret body) = Run.call args ret body.ext body.runR σ := rfl

end Equations

/-! ## Examples

`Semantics.lean`'s runs, on the scoped programs: each block resolved,
quoted and declared (`Prog.defineCore`), then run by the kernel. -/

section Examples

private def guardLow : Solidity.Prog StandardExample := sol[StandardExample]{ require(age > 3); }
private def assertLow : Solidity.Prog StandardExample := sol[StandardExample]{ assert(age > 3); }
private def incOrder : Solidity.Prog TestSuite := sol[TestSuite]{ uint i = 1; uint x = i++ + i;
  assert(x == 2); assert(i == 2); }
private def indexOrder : Solidity.Prog TestSuite := sol[TestSuite]{ uint i = 0; values.push(100);
  values.push(100); values.push(100); values[++i] = ++i; assert(values[2] == 1); }
private def countUp : Solidity.Prog StandardExample := sol[StandardExample]{
  uint i = 0; while (i < 3) { uint j = i + 1; i = j; } assert(i == 3); }

open Lean Elab Command in
run_cmd liftCoreM do
  let defs : List (Lean.Name × Lean.Name × Option String) := [
    (`guardLowCore, ``StandardExample,
      ← Prog.defineCore `Solidity.Core.guardLowCore ``StandardExample [] guardLow),
    (`assertLowCore, ``StandardExample,
      ← Prog.defineCore `Solidity.Core.assertLowCore ``StandardExample [] assertLow),
    (`incOrderCore, ``TestSuite,
      ← Prog.defineCore `Solidity.Core.incOrderCore ``TestSuite [] incOrder),
    (`indexOrderCore, ``TestSuite,
      ← Prog.defineCore `Solidity.Core.indexOrderCore ``TestSuite [] indexOrder),
    (`countUpCore, ``StandardExample,
      ← Prog.defineCore `Solidity.Core.countUpCore ``StandardExample [] countUp)]
  for (n, cn, err) in defs do
    if let some e := err then throwError "{n} ({cn}): {e}"

/-- A state of the old interpreter's, with no locals. -/
def State.ofSem (τ : Semantics.State) : State C [] := State.ofGlob τ ()

/-- A block resolved from no locals and run, then read by `f`: compiled, for
`#eval`. -/
def runResolved {C : Contract} [FreshNames] (σ : Semantics.State) (P : Solidity.Prog C)
    (f : {Γ : Ctx} → State C Γ → Res α) : Res α :=
  match Prog.resolve [] P with
  | .ok ⟨_, P'⟩ => do f (← Prog.run (State.ofSem σ) P')
  | .error _ => .error .stuck

/-! `x = 10` through an alias (`Semantics.lean`'s `aliasWrite`), by `#eval`:
its storage overlay does not reduce in the kernel, by either interpreter. -/

/-- info: Except.ok (Solidity.Semantics.SVal.prim (Solidity.Semantics.PrimVal.int 10)) -/
#guard_msgs in
#eval runResolved Semantics.State.exampleStore aliasWrite fun τ =>
  τ.glob.findStorage "alice" [.field "age"]

/-- A failing guard reverts. -/
example : Prog.run (State.ofSem Semantics.State.exampleStore) guardLowCore = .error .revert := rfl

/-- A failing assertion panics. -/
example : Prog.run (State.ofSem Semantics.State.exampleStore) assertLowCore = .error .panic := rfl

/-- solc's order of `++` inside an expression (two of `Semantics.lean`'s
three: the third, `matrix[k][k++]`, does not reduce in the kernel, by either
interpreter). -/
example : ((Prog.run (State.ofSem Semantics.State.testSuiteStore) incOrderCore).isOk,
    (Prog.run (State.ofSem Semantics.State.testSuiteStore) indexOrderCore).isOk) =
    (true, true) := by
  decide +kernel

/-- The calls of `CallsExample`: `addTwo(3)` is `5`, `larger(5, 7)` is `7`. -/
example : (do
    let τ ← Prog.run (State.ofSem { storage := CallsExample.initStorage }) callsCore
    pure ((Env.get .here τ.env : Value), (Env.get (.there .here) τ.env : Value))) =
    .ok (.int 7, .int 5) := rfl

/-- A loop whose body declares a local each iteration, popped at its end:
done at the fourth iteration. -/
example : (Prog.run (State.ofSem Semantics.State.exampleStore) countUpCore).isOk = true := by
  unfold countUpCore
  rw [Prog.run_cons_ok rfl, Prog.run_loop_of_iterN (n := 4) rfl]
  rfl

end Examples

end Solidity.Core
