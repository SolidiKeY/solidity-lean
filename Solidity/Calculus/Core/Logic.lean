import Solidity.Calculus.Core.Step
import Solidity.Semantics.Core
import Solidity.Update
import Solidity.Theory.Observe
import Solidity.Typing.Soundness
import Solidity.Semantics.Core.TypedRunFrame

/-!
# What a scoped formula means

The scoped formulas of `Calculus/Core/Fml.lean` read over the typed state
(`TState`, `Semantics/Core/TypedState.lean`) and the typed run (`Prog.trun`,
`Frames.trun`): `holds`, `Valid`.

* A term means what `Update.lean`'s term means on the state's erasure
  (`TState.erase`, M3's `State C Γ`, `Semantics/Core.lean`): a local is read
  by its position, a symbol on the global part (`State.glob`); its symbols
  are untyped until the closer is ported (M6c).
* An update is parallel (every right-hand side read in the state it is
  applied in), applied to the erasure, and leaves the context `Δ` its type
  says: a declaration pushes, a pop drops a suffix, a `drop` thins.  What
  follows it is read in every typed state that erases to the state it ends
  in and whose heap typing extends the one it is applied in, as a typed
  run's does (`Out.ext`).  The rules' updates end in the erasure of the
  state the statement's typed run ends in, so that state is one of them; an
  update that ends in no typed state (a value of another type) says
  nothing.
* A modality runs the program and its frames with the typed run: a `bool`
  local holds a `bool`, so a branch is never stuck and the diamond needs no
  guard.  Both modalities accept a run exhausted (a push at the bound,
  decision 15); neither a panic.
* The binders range over typed values: `∀ x` over the values of its type, a
  hidden binder (`Fml.bind`) over what a local of its type may hold in the
  state's heap, `{anon(xs)}` over typed values of the locals, `{havoc}` over
  typed storages.

A hidden binder at a memory type ranges over the references the heap
typing gives that type and over `none`, an unset local (decision 17'):
`memoryLocalDeclInitDrop`'s premise needs its instance at `none`, from which
`T memory mv = r;` runs as `mv = r;`, and which no typed reference gives
when `r` allocates.  So every type has a value
(`LTy.tdenote_nonempty`) and the binder is universal under both modalities
(`Modality.forallB`).

Before the formulas: the term, update and run lemmas on the erasure that the
rules' soundness (`Calculus/Core/Sound*.lean`) reads, M3's run being the
bridge (`Stmt.trun_erase`) from the typed run to `Update.lean`'s terms.
-/

namespace Solidity.Core
open Semantics (Value SVal MVal Seg Halt Res lookupBy setBy allocDefault applyUnOp)
open Solidity (evalBinop unopCheck)
open Theory Theory.StValue
open Solidity (Srt Op0 Op1 Op2 Op3 Modality IntOp)

variable {C : Contract}

/-! ## Terms -/

section Terms

variable {Γ : Ctx}

/-- A term read by the interpreter in `σ`: a local by its position, a symbol
on the global part. -/
def Tm.eval (σ : State C Γ) : {s : Srt} → Tm C Γ s → s.Ev
  | _, .pvV i => pure (Env.get i σ.env)
  | _, .pvP i => aliasPath σ i
  | _, .pvS i => pure { σ.glob with storage := Env.get i σ.env }
  | _, .pvI i => memRef σ i
  | _, .netOf i a => do
    let l : List (Int × Int) := Env.get i σ.env
    pure (.int ((lookupBy (← (← a.eval σ).asInt) l).getD 0))
  | _, .app0 o => o.eval σ.glob
  | _, .app1 o _ a => o.eval σ.glob (a.eval σ)
  | _, .app2 o a b => o.eval σ.glob (a.eval σ) (b.eval σ)
  | _, .app3 o a b c => o.eval σ.glob (a.eval σ) (b.eval σ) (c.eval σ)

/-- A term in the Theory, over `State.abs σ.glob` (`Update.lean`'s
`Tm.denote`). -/
def Tm.denote (σ : State C Γ) : {s : Srt} → Tm C Γ s → s.Den
  | _, .pvV i => .prim (Env.get i σ.env)
  | _, .pvP i => match aliasPath σ i with
    | .ok (r, segs) => rootPath r segs
    | .error _ => []
  | _, .pvS i => SVal.abs.fields (Env.get i σ.env)
  | _, .pvI _ => ()
  | _, .netOf i a => match a.denote σ with
    | .prim (.int n) => .prim (.int ((lookupBy n (Env.get i σ.env : List (Int × Int))).getD 0))
    | _ => .st .mtSt
  | _, .app0 o => o.denote σ.glob
  | _, .app1 o _ a => o.denote σ.glob (a.denote σ)
  | _, .app2 o a b => o.denote σ.glob (a.eval σ) (b.eval σ) (a.denote σ) (b.denote σ)
  | _, .app3 o a b c => o.denote (a.denote σ) (b.denote σ) (c.denote σ)

end Terms

/-! ## Updates -/

section Updates

/-- A scope's locals dropped by a thinning: the ones `Γ` keeps. -/
def Env.thin : {Γ Δ : Ctx} → Thin Γ Δ → Env C Δ → Env C Γ
  | _, _, .refl, e => e
  | _, _, .keep h, e => (e.1, Env.thin h e.2)
  | _, _, .drop h, e => Env.thin h e.2

/-- A state's locals thinned. -/
def State.thin {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) : State C Γ :=
  σ.withEnv (Env.thin h σ.env)

variable {Γ : Ctx}

/-- What a local is set to, read in `σ₀`. -/
def Rhs.eval (σ₀ : State C Γ) : {t : LTy} → Rhs C Γ t → Res (t.Denote C)
  | _, .val t => t.eval σ₀
  | _, .path p => do pure (some (← p.eval σ₀))
  | _, .unset => pure none
  | _, .mref i => do pure (some (← i.eval σ₀))
  | _, .store s => do pure (← s.eval σ₀).storage
  | _, .saveNet => pure σ₀.net
  | _, .saveNetMt => pure []

/-- One assigning element: its right-hand sides read in `σ₀`, the write
into `τ` (`Update.lean`'s `UpdElem.write`). -/
def UpdElem.write {Δ : Ctx} (σ₀ : State C Γ) : UpdElem C Γ Δ → State C Δ → Res (State C Δ)
  | .local i r, τ => do pure (τ.setLocal i (← r.eval σ₀))
  | .storage s, τ => do
    let st := (← s.eval σ₀).storage
    pure (τ.withGlob { τ.glob with storage := st })
  | .memory m, τ => do
    let μ ← m.eval σ₀
    pure (τ.withGlob { τ.glob with heap := μ.heap, nextId := μ.nextId })
  | .selfBalance op a, τ => do
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with selfBalance := op.apply σ₀.selfBalance amt })
  | .net r op a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with net := setBy addr (op.apply (τ.glob.getNet addr) amt) τ.net })
  | .pay r a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    if amt < 0 then .error .revert
    else pure (τ.withGlob { τ.glob with
      net := if addr = σ₀.tx.selfAddress then τ.net else setBy addr (τ.glob.getNet addr - amt) τ.net })
  | .netMt r a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with net := [(addr, amt)] })
  | .setBalance a, τ => do
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with selfBalance := amt })

/-- The state an update applied in `σ₀` leaves, in the context its type
says. -/
def Upd.apply (σ₀ : State C Γ) : {Δ : Ctx} → Upd C Γ Δ → Res (State C Δ)
  | _, .nil => pure σ₀
  | _, .snoc U e => do e.write σ₀ (← U.apply σ₀)
  | _, .decl U _ r => do
    let τ ← U.apply σ₀
    pure (τ.push (← r.eval σ₀))
  | _, .pop U h => (U.apply σ₀).map (State.drop h)
  | _, .drop U h => (U.apply σ₀).map (State.thin h)

end Updates

/-! ## Formulas -/

/-- `p` after an outcome under `m`: `p` of the state, or `m.onHalt`. -/
def _root_.Solidity.Modality.afterC {α : Type} (m : Modality) (p : α → Prop) : Res α → Prop
  | .ok τ => p τ
  | .error _ => m.onHalt

/-- `p` after a run under `m`: as `afterC`, and the run did not panic. -/
def _root_.Solidity.Modality.afterRunC {α : Type} (m : Modality) (p : α → Prop) (r : Res α) : Prop :=
  m.afterC p r ∧ r ≠ .error .panic

/-- What the frames do after the program: the rest run, a scope's locals
popped or dropped. -/
def Frames.run {Γ₀ : Ctx} : {Γ : Ctx} → State C Γ → Frames C Γ Γ₀ → Res (State C Γ₀)
  | _, σ, .nil => pure σ
  | _, σ, .seq ω κ => do Frames.run (← Prog.run σ ω) κ
  | _, σ, .pop _ h κ => Frames.run (σ.drop h) κ
  | _, σ, .drop h κ => Frames.run (σ.thin h) κ

/-- The locals `xs` set as `b` says: a loop body's frame anonymised. -/
def State.anon {Γ : Ctx} (σ : State C Γ) (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.Denote C) : State C Γ :=
  xs.foldl (fun τ x => τ.setLocal x.2 (b x)) σ

/-! ## Runs with their frames -/

section Shapes

variable {Γ Γ' Γ₁ Γ₀ : Ctx} {m : Modality}

/-- The outcome of `s` and then the rest: the run of `s; ω` and the frames. -/
theorem run_cons_frames (s : Stmt C Γ Γ') (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (σ : State C Γ) :
    (do Frames.run (← Prog.run σ (.cons s ω)) κ) =
      (do let τ ← s.run σ; Frames.run (← Prog.run τ ω) κ) := by
  rw [Prog.run_cons]
  cases s.run σ <;> rfl

/-- An outcome that is the same after `r` as after `r'`, `r` not a panic,
satisfies the same: the step every shape ends with. -/
theorem afterRunC_bind {α β : Type} {p : β → Prop} {r r' : Res α} (f : α → Res β)
    (hr : r = r') (hp : r' ≠ .error .panic) :
    m.afterC (fun a => m.afterRunC p (f a)) r → m.afterRunC p (r'.bind f) := by
  subst hr
  cases r with
  | ok a => exact id
  | error e => exact fun h => ⟨h, fun h' => hp (congrArg Except.error (Except.error.inj h'))⟩

/-- A block's run, its locals popped, then the rest and the frames: the
frame a branch ends with (`pop b P.ext`). -/
theorem run_block_frames {Δ : Ctx} (b : BlockKind) (P : Prog C Γ Δ) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (σ : State C Γ) :
    (do Frames.run (← Prog.run σ P) (.pop b P.ext (.seq ω κ))) =
      (do let τ ← (Prog.run σ P).map (State.drop P.ext); Frames.run (← Prog.run τ ω) κ) := by
  cases Prog.run σ P <;> rfl

end Shapes

/-! ## A shifted part reads as it did

A rule reads the parts of its `\find` under its fresh locals (`Val.up` and
its kin): pushed a local, the state reads them as before. -/

section Shift

variable {Γ : Ctx} {t : LTy}

theorem State.glob_push (σ : State C Γ) (w : t.Denote C) : (σ.push w).glob = σ.glob := rfl

theorem Simple.eval_up {p : PrimTy} (s : Simple C Γ p) (σ : State C Γ) (w : t.Denote C) :
    (s.up (t := t)).eval (σ.push w) = s.eval σ := by
  cases s <;> rfl

theorem aliasPath_there {R : RefTy} (i : Idx Γ (.alias R)) (σ : State C Γ) (w : t.Denote C) :
    aliasPath (σ.push w) i.there = aliasPath σ i := rfl

mutual

theorem SPath.resolve_up (σ : State C Γ) (w : t.Denote C) : {T : Ty} → (b : SPath C Γ T) →
    (b.up (t := t)).resolve (σ.push w) = b.resolve σ
  | _, .alias _ => rfl
  | _, .loc l => Loc.resolve_up σ w l

theorem Loc.resolve_up (σ : State C Γ) (w : t.Denote C) : {T : Ty} → (l : Loc C Γ T) →
    (l.up (t := t)).resolve (σ.push w) = l.resolve σ
  | _, .root .. => rfl
  | _, .field b f h => by
    show (do let (r, segs) ← b.up.resolve (σ.push w); pure (r, segs ++ [Seg.field f])) = _
    rw [SPath.resolve_up σ w b]; rfl
  | _, .index it b i => by
    show (do
      let (r, segs) ← b.up.resolve (σ.push w)
      let i ← (← i.up.eval (σ.push w)).keyAt _
      (σ.push w).glob.checkIndex r segs i
      pure (r, segs ++ [Seg.at i])) = _
    rw [SPath.resolve_up σ w b, Val.eval_up σ w i]; rfl

theorem MPath.mval_up (σ : State C Γ) (w : t.Denote C) : {T : Ty} → (b : MPath C Γ T) →
    (b.up (t := t)).mval (σ.push w) = b.mval σ
  | _, .var .. => rfl
  | _, .loc l => MLoc.read_up σ w l

theorem MLoc.read_up (σ : State C Γ) (w : t.Denote C) : {T : Ty} → (l : MLoc C Γ T) →
    (l.up (t := t)).read (σ.push w) = l.read σ
  | _, .field b f h => by
    show (do
      let id ← (← b.up.mval (σ.push w)).asRef
      match ← (σ.push w).glob.getObj id with
      | .struct fields =>
        match lookupBy f fields with
        | some v => pure v
        | none => .error .stuck
      | .array _ _ => .error .stuck) = _
    rw [MPath.mval_up σ w b]; rfl
  | _, .index a b i => by
    show (do
      let id ← (← b.up.mval (σ.push w)).asRef
      let iv ← (← i.up.eval (σ.push w)).asInt
      match ← (σ.push w).glob.getObj id with
      | .array elems _ =>
        if h : 0 ≤ iv ∧ iv.toNat < elems.length then pure (elems.get ⟨iv.toNat, h.2⟩)
        else .error .revert
      | .struct _ => .error .stuck) = _
    rw [MPath.mval_up σ w b, Val.eval_up σ w i]; rfl

theorem Val.eval_up (σ : State C Γ) (w : t.Denote C) : {p : PrimTy} → (v : Val C Γ p) →
    (v.up (t := t)).eval (σ.push w) = v.eval σ
  | _, .simple s => Simple.eval_up s σ w
  | _, .read l => by
    show (do
      let (r, segs) ← l.up.resolve (σ.push w)
      (← (σ.push w).glob.findStorage r segs).asValue) = _
    rw [Loc.resolve_up σ w l]; rfl
  | _, .binop op _ _ a b => by
    show (do evalBinop op _ (← a.up.eval (σ.push w)) (b.up.eval (σ.push w))) = _
    rw [Val.eval_up σ w a, Val.eval_up σ w b]; rfl
  | _, .unop op _ _ a => by
    show (do unopCheck op _ (← applyUnOp op (← a.up.eval (σ.push w)))) = _
    rw [Val.eval_up σ w a]; rfl
  | _, .ternary c a b => by
    show (do pickBranch (← c.up.eval (σ.push w)) (a.up.eval (σ.push w)) (b.up.eval (σ.push w))) = _
    rw [Val.eval_up σ w c, Val.eval_up σ w a, Val.eval_up σ w b]; rfl
  | _, .readMem l => by
    show (do (← l.up.read (σ.push w)).asValue) = _
    rw [MLoc.read_up σ w l]; rfl
  | _, .len b _ => by
    show (do
      let (r, segs) ← b.up.resolve (σ.push w)
      arrayLen (σ.push w).glob r segs) = _
    rw [SPath.resolve_up σ w b]; rfl
  | _, .mlen b _ => by
    show (do memArrayLen (σ.push w).glob (← (← b.up.mval (σ.push w)).asRef)) = _
    rw [MPath.mval_up σ w b]; rfl

end

end Shift

/-! ## Rules -/

section Rules

variable {Γ Γ₁ Γ₀ : Ctx} {m : Modality}

/-- A simple value lowered reads as it evaluates. -/
theorem Simple.eval_lower {p : PrimTy} (s : Simple C Γ p) (σ : State C Γ) :
    s.lower.eval σ = s.eval σ := by
  cases s <;> rfl

/-- A simple value denotes what it evaluates to. -/
theorem Simple.denote_lower {p : PrimTy} (se : Simple C Γ p) (σ : State C Γ) {v : Value}
    (h : se.eval σ = .ok v) : se.lower.denote σ = .prim v := by
  cases se <;> cases h <;> rfl

end Rules

/-! ## Formulas -/

/-- `p` after a typed run under `m` (`Modality.afterRunC`): `p` of the state
it ends in, `m.onTHalt` on a halt (both modalities accept `exhausted`,
decision 15), and no panic. -/
def _root_.Solidity.Modality.afterRunTR {α : Type} (m : Modality) (p : α → Prop) (r : TRes α) :
    Prop :=
  (match r with
    | .ok a => p a
    | .error e => m.onTHalt e) ∧ r ≠ .error .panic

/-- The state a modality's program, then its frames, end in. -/
def Prog.trunFrames {Γ Γ₁ Γ₀ : Ctx} (σ : TState C Γ) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) :
    TRes (TState C Γ₀) := do
  let o ← Prog.trun σ P
  let o' ← Frames.trun o.st κ
  pure o'.st

/-- **Whether `φ` holds in the typed state `σ`.** -/
def holds : {Γ : Ctx} → TState C Γ → Fml C Γ → Prop
  | _, _, .tt => True
  | _, σ, .eq a b => Theory.StValue.Equiv (a.denote σ.erase) (b.denote σ.erase)
  | _, σ, .defined t => ∃ x, t.eval σ.erase = .ok x
  | _, σ, .not φ => ¬ holds σ φ
  | _, σ, .and φ ψ => holds σ φ ∧ holds σ ψ
  | _, σ, .imp φ ψ => holds σ φ → holds σ ψ
  | _, σ, .upd m U φ =>
    m.afterC (fun τ => ∀ σ' : TState C _, σ'.erase = τ → σ.H <+: σ'.H → holds σ' φ)
      (U.apply σ.erase)
  | _, σ, .modal m P κ φ => m.afterRunTR (holds · φ) (Prog.trunFrames σ P κ)
  | _, σ, .havoc φ => ∀ st nt, holds (σ.havoc st nt) φ
  | _, σ, .all _ p φ => ∀ v : p.Denote, holds (σ.push (t := .val p) v) φ
  | _, σ, .bind m _ t φ => m.forallB fun v : t.TDenote C σ.H => holds (σ.push v) φ
  | _, σ, .anon xs φ => ∀ b, holds (σ.anon xs b) φ

/-- Every local's type has a value in every typed state: an alias and a
memory local unset among them (decision 17'). -/
theorem LTy.tdenote_nonempty {H : HTy} : (t : LTy) → Nonempty (t.TDenote C H)
  | .val p => ⟨PrimTy.dflt p⟩
  | .alias _ => ⟨none⟩
  | .mem _ => ⟨none⟩
  | .old => ⟨Storage.init C⟩
  | .oldNet => ⟨[]⟩

/-- Valid over the typed states: true in every typed state of the empty
context. -/
def Valid (φ : Fml C []) : Prop := ∀ σ : TState C [], holds σ φ

end Solidity.Core
