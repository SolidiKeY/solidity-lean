import Solidity.Semantics
import Solidity.Syntax.Quote

/-!
# The erased state and its evaluators over the scoped syntax

What the closer's untyped terms read (`docs/intrinsic.md`, M3, decision 40):
a state carries the locals of its context `Γ`, `Env C Γ`, a type computed
from `Γ` (`Unit`, then one component per local, innermost first), beside
`Semantics.lean`'s untyped global part (`State.glob`).  A typed state erases
to one (`State.erase`, `Semantics/State.lean`), and the
expressions are read on it by the evaluators here (`Val.eval`,
`Loc.resolve`, `MLoc.read`, …), which call `Semantics.lean`'s operations on
the global part; the effects a step has on it (`OpLoc.store`, `MLoc.write`,
`MRhs.eval`, `CallRet.enter`, …) are what a typed step erases to
(`Semantics/StepErase.lean`).  There is no run of a statement here:
the typed run (`Semantics/Run.lean`) is the only one.  An
evaluator meets a value of another shape than its type (a `bool` where a
`uint` is read) only on a state no typed one erases to, and then reads
`undef`, the term model's ill-sorted value.

Where the kernel evaluates: `Env`'s functions recurse on `Idx`/`Ext` by
`casesOn` (Gate G0, condition 1).
-/

namespace Solidity

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
structure EState (C : Contract) (Γ : Ctx) where
  storage : List (Name × SVal)
  heap : List (Nat × Semantics.MObj) := []
  nextId : Nat := 0
  env : Env C Γ
  net : List (Int × Int) := []
  selfBalance : Int := 0
  tx : Semantics.TxEnv := {}

namespace EState

/-- Everything but the locals, as `Semantics.lean`'s operations take it. -/
def glob {Γ : Ctx} (σ : EState C Γ) : Semantics.State :=
  { storage := σ.storage, heap := σ.heap, nextId := σ.nextId, net := σ.net,
    selfBalance := σ.selfBalance, tx := σ.tx }

/-- A global part with locals. -/
def ofGlob {Γ : Ctx} (τ : Semantics.State) (e : Env C Γ) : EState C Γ :=
  { storage := τ.storage, heap := τ.heap, nextId := τ.nextId, env := e, net := τ.net,
    selfBalance := τ.selfBalance, tx := τ.tx }

/-- The global part replaced. -/
def withGlob {Γ : Ctx} (σ : EState C Γ) (τ : Semantics.State) : EState C Γ := ofGlob τ σ.env

/-- The locals replaced, in another context. -/
def withEnv {Γ Δ : Ctx} (σ : EState C Γ) (e : Env C Δ) : EState C Δ :=
  { storage := σ.storage, heap := σ.heap, nextId := σ.nextId, env := e, net := σ.net,
    selfBalance := σ.selfBalance, tx := σ.tx }

/-- A local declared. -/
def push {Γ : Ctx} {t : LTy} (σ : EState C Γ) (v : t.Denote C) : EState C (t :: Γ) :=
  σ.withEnv (v, σ.env)

/-- A local set. -/
def setLocal {Γ : Ctx} {t : LTy} (σ : EState C Γ) (i : Idx Γ t) (v : t.Denote C) : EState C Γ :=
  σ.withEnv (Env.set i v σ.env)

/-- A scope's locals popped. -/
def drop {Γ Δ : Ctx} (h : Ext Γ Δ) (σ : EState C Δ) : EState C Γ := σ.withEnv (Env.drop h σ.env)

/-- A global state with no locals. -/
def ofSem (τ : Semantics.State) : EState C [] := EState.ofGlob τ ()

end EState

/-! ## Expressions -/

section Eval

variable {Γ : Ctx}

/-- The value a simple value denotes: a literal, a local's, the
environment's. -/
def Simple.eval (σ : EState C Γ) {p : PrimTy} : Simple C Γ p → Res Value
  | .lit n _ => pure (.int n)
  | .bool b => pure (.bool b)
  | .local i => pure (Env.get i σ.env)
  | .env k _ => pure (.int (σ.glob.envVal k))

/-- The path an alias is bound to; an unset one reverts. -/
def aliasPath (σ : EState C Γ) {R : RefTy} (i : Idx Γ (.alias R)) : Res (Name × List Seg) :=
  match (Env.get i σ.env : Option (Name × List Seg)) with
  | some p => pure p
  | none => .error .revert

/-- The object a memory local names; an unset one reverts, as an unset
alias does (decision 17'). -/
def memRef (σ : EState C Γ) {R : RefTy} (i : Idx Γ (.mem R)) : Res Nat :=
  match (Env.get i σ.env : Option Nat) with
  | some id => pure id
  | none => .error .revert

mutual

/-- The storage path a path denotes in `σ`. -/
def SPath.resolve (σ : EState C Γ) : {T : Ty} → SPath C Γ T → Res (Name × List Seg)
  | _, .alias i => aliasPath σ i
  | _, .loc l => l.resolve σ

def Loc.resolve (σ : EState C Γ) : {T : Ty} → Loc C Γ T → Res (Name × List Seg)
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
def MPath.mval (σ : EState C Γ) : {T : Ty} → MPath C Γ T → Res MVal
  | _, .var i _ => do pure (.ref (← memRef σ i))
  | _, .loc l => l.read σ

def MLoc.read (σ : EState C Γ) : {T : Ty} → MLoc C Γ T → Res MVal
  | _, .field b f _ => do
    let id ← (← b.mval σ).asRef
    match ← σ.glob.getObj id with
    | .struct fields =>
      match lookupBy f fields with
      | some v => pure v
      | none => .error .undef
    | .array _ _ => .error .undef
  | _, .index _ b i => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    match ← σ.glob.getObj id with
    | .array elems _ =>
      if h : 0 ≤ iv ∧ iv.toNat < elems.length then pure (elems.get ⟨iv.toNat, h.2⟩)
      else .error .revert
    | .struct _ => .error .undef

/-- The value a value expression denotes in `σ`. -/
def Val.eval (σ : EState C Γ) : {p : PrimTy} → Val C Γ p → Res Value
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
def Src.value (σ : EState C Γ) {T : Ty} : Src C Γ T → Res SVal
  | .val v => do pure (← v.eval σ).toSVal
  | .copy p _ => do
    let (r, segs) ← p.resolve σ
    σ.glob.findStorage r segs

/-- What a push appends: the slot, or its argument laid on fresh slots. -/
def Src.pushVal (σ : EState C Γ) {T : Ty} : Option (Src C Γ T) → SVal → Res SVal
  | none, slot => pure slot
  | some r, _ => do pure (← r.value σ).strip

/-- `l = mv` into a memory location. -/
def MLoc.write (σ : EState C Γ) (mv : MVal) {T : Ty} : MLoc C Γ T → Res (EState C Γ)
  | .field b f _ => do
    let id ← (← b.mval σ).asRef
    σ.withGlob <$> memWriteField σ.glob id f mv
  | .index _ b i => do
    let id ← (← b.mval σ).asRef
    let iv ← (← i.eval σ).asInt
    σ.withGlob <$> memWriteIndex σ.glob id iv mv

/-- The slot a memory source writes. -/
def MSrc.mval (σ : EState C Γ) {T : Ty} : MSrc C Γ T → Res MVal
  | .val v => do pure (← v.eval σ).toMVal
  | .ref p => do pure (.ref (← (← p.mval σ).asRef))

/-- The object a memory right-hand side names, and the state its
allocation leaves: an object by identity, a deep copy, a fresh array. -/
def MRhs.eval (σ : EState C Γ) {R : RefTy} : MRhs C Γ R → Res (EState C Γ × Nat)
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
def ARhs.eval (σ : EState C Γ) {R : RefTy} : ARhs C Γ R → Res (EState C Γ × (Name × List Seg))
  | .path p => do pure (σ, ← p.resolve σ)
  | .push b _ => do
    let (root, segs) ← b.resolve σ
    let (τ, n) ← pushPlaceAt σ.glob (.ref R) root segs
    pure (σ.withGlob τ, (root, segs ++ [.at n]))

/-- The address of a memory location. -/
def MLoc.addr (σ : EState C Γ) {T : Ty} : MLoc C Γ T → Res Semantics.Addr
  | .field b f _ => do pure (.memoryField (← (← b.mval σ).asRef) f)
  | .index _ b i => do
    let id ← (← b.mval σ).asRef
    pure (.memoryIndex id (← (← i.eval σ).asInt))

/-- A memory write is a write at its location's address. -/
theorem MLoc.write_eq (σ : EState C Γ) (mv : MVal) {T : Ty} (l : MLoc C Γ T) :
    l.write σ mv = l.addr σ >>= fun a => σ.withGlob <$> Solidity.writeAddr σ.glob mv a := by
  cases l <;> simp only [MLoc.write, MLoc.addr, Solidity.writeAddr, bind_assoc, pure_bind]

/-- `x ⊕= v` on a local. -/
def opLocal (σ : EState C Γ) (op : BinOp) (p : PrimTy) (i : Idx Γ (.val p)) (v : Value) :
    Res (EState C Γ) := do
  let new ← applyBinOp op (Env.get i σ.env) v
  let new ← checkArith (.prim p) new
  pure (σ.setLocal i new)

/-- A compound assignment's write of `v` into its target. -/
def OpLoc.store (σ : EState C Γ) (op : BinOp) : {p : PrimTy} → OpLoc C Γ p → Value →
    Res (EState C Γ)
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
def bumpLocal (σ : EState C Γ) (op : IncDec) (p : PrimTy) (i : Idx Γ (.val p)) :
    Res (EState C Γ × Value) := do
  let old : Value := Env.get i σ.env
  let oldInt ← old.asInt
  let new ← checkArith (.prim p) (.int (if op.isIncrement then oldInt + 1 else oldInt - 1))
  pure (σ.setLocal i new, if op.isPre then new else old)

/-- A global step's state and value, with the locals. -/
private def withGlob₂ (σ : EState C Γ) : Semantics.State × Value → EState C Γ × Value
  | (τ, v) => (σ.withGlob τ, v)

/-- `l++`: the state it leaves, and its value. -/
def OpLoc.bump (σ : EState C Γ) (op : IncDec) : {p : PrimTy} → OpLoc C Γ p →
    Res (EState C Γ × Value)
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
def sendAt (σ : EState C Γ) (pv : Idx Γ (.val .bool)) (addr amt : Int) : Res (EState C Γ) :=
  if amt < 0 then .error .revert
  else match lookupBy (sendKey addr amt) σ.tx.ext with
    | none | some (.ok _) => .ok ((σ.withGlob (σ.glob.pay addr amt)).setLocal pv (.bool true))
    | some _ => .ok (σ.setLocal pv (.bool false))

/-- The call as it is made, its receiver and arguments evaluated. -/
def ExtCall.key (σ : EState C Γ) (c : ExtCall C Γ) : Res Semantics.ExtKey := do
  let a ← (← c.addr.eval σ).asInt
  let vs ← c.args.mapM fun a => a.2.eval σ
  pure ⟨a, c.fn, vs⟩

/-- A call's arguments, each read in the caller's state, in order. -/
def Args.eval (σ : EState C Γ) : {ps : Ctx} → Args C Γ ps → Res (Env C ps)
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
  | .int _ => .error .undef

/-- An assertion's outcome: `true` goes on, `false` panics. -/
def assertOk {α : Type} (v : Value) (a : α) : Res α :=
  match v with
  | .bool true => pure a
  | .bool false => .error .panic
  | .int _ => .error .undef

/-! ## Examples

Scoped programs, each block resolved, quoted and declared
(`Prog.defineCore`), which the typed run's examples run
(`Semantics/Run.lean`). -/

section Examples

private def guardLow : Solidity.Surface.Prog StandardExample := sol[StandardExample]{ require(age > 3); }
private def assertLow : Solidity.Surface.Prog StandardExample := sol[StandardExample]{ assert(age > 3); }
private def incOrder : Solidity.Surface.Prog TestSuite := sol[TestSuite]{ uint i = 1; uint x = i++ + i;
  assert(x == 2); assert(i == 2); }
private def indexOrder : Solidity.Surface.Prog TestSuite := sol[TestSuite]{ uint i = 0; values.push(100);
  values.push(100); values.push(100); values[++i] = ++i; assert(values[2] == 1); }

open Lean Elab Command in
run_cmd liftCoreM do
  let defs : List (Lean.Name × Lean.Name × Option String) := [
    (`guardLowCore, ``StandardExample,
      ← Prog.defineCore `Solidity.guardLowCore ``StandardExample [] guardLow),
    (`assertLowCore, ``StandardExample,
      ← Prog.defineCore `Solidity.assertLowCore ``StandardExample [] assertLow),
    (`incOrderCore, ``TestSuite,
      ← Prog.defineCore `Solidity.incOrderCore ``TestSuite [] incOrder),
    (`indexOrderCore, ``TestSuite,
      ← Prog.defineCore `Solidity.indexOrderCore ``TestSuite [] indexOrder)]
  for (n, cn, err) in defs do
    if let some e := err then throwError "{n} ({cn}): {e}"

end Examples

end Solidity
