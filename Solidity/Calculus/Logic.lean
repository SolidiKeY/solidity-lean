import Solidity.Calculus.Step
import Solidity.Semantics.Erased
import Solidity.Update
import Solidity.Theory.Observe
import Solidity.Typing.Soundness
import Solidity.Semantics.RunFrame

/-!
# What a scoped formula means

The scoped formulas of `Calculus/Fml.lean` read over the typed state
(`State`, `Semantics/State.lean`) and the typed run (`Prog.run`,
`Frames.run`): `holds`, `Valid`.

* A term means what `Update.lean`'s term means on the state's erasure
  (`State.erase`, M3's `State C Γ`, `Semantics/Erased.lean`): a local is read
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

Before the formulas: the term and update lemmas on the erasure that the
rules' soundness (`Calculus/Sound*.lean`) reads, each typed step read
on the erasure (`Semantics/StepErase.lean`) being what relates the
typed run to `Update.lean`'s terms.
-/

namespace Solidity
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
def Tm.eval (σ : EState C Γ) : {s : Srt} → Tm C Γ s → s.Ev
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
def Tm.denote (σ : EState C Γ) : {s : Srt} → Tm C Γ s → s.Den
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
def EState.thin {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : EState C Δ) : EState C Γ :=
  σ.withEnv (Env.thin h σ.env)

variable {Γ : Ctx}

/-- What a local is set to, read in `σ₀`. -/
def Rhs.eval (σ₀ : EState C Γ) : {t : LTy} → Rhs C Γ t → Res (t.Denote C)
  | _, .val t => t.eval σ₀
  | _, .path p => do pure (some (← p.eval σ₀))
  | _, .unset => pure none
  | _, .mref i => do pure (some (← i.eval σ₀))
  | _, .store s => do pure (← s.eval σ₀).storage
  | _, .saveNet => pure σ₀.net
  | _, .saveNetMt => pure []

/-- One assigning element: its right-hand sides read in `σ₀`, the write
into `τ` (`Update.lean`'s `UpdElem.write`). -/
def UpdElem.write {Δ : Ctx} (σ₀ : EState C Γ) : UpdElem C Γ Δ → EState C Δ → Res (EState C Δ)
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
def Upd.apply (σ₀ : EState C Γ) : {Δ : Ctx} → Upd C Γ Δ → Res (EState C Δ)
  | _, .nil => pure σ₀
  | _, .snoc U e => do e.write σ₀ (← U.apply σ₀)
  | _, .decl U _ r => do
    let τ ← U.apply σ₀
    pure (τ.push (← r.eval σ₀))
  | _, .pop U h => (U.apply σ₀).map (EState.drop h)
  | _, .drop U h => (U.apply σ₀).map (EState.thin h)

end Updates

/-! ## Formulas -/

/-- `p` after an outcome under `m`: `p` of the state, or `m.onHalt`. -/
def _root_.Solidity.Modality.afterC {α : Type} (m : Modality) (p : α → Prop) : Res α → Prop
  | .ok τ => p τ
  | .error _ => m.onHalt

/-- The locals `xs` set as `b` says: a loop body's frame anonymised. -/
def EState.anon {Γ : Ctx} (σ : EState C Γ) (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.Denote C) : EState C Γ :=
  xs.foldl (fun τ x => τ.setLocal x.2 (b x)) σ

/-! ## Rules -/

section Rules

variable {Γ Γ₁ Γ₀ : Ctx} {m : Modality}

/-- A simple value lowered reads as it evaluates. -/
theorem Simple.eval_lower {p : PrimTy} (s : Simple C Γ p) (σ : EState C Γ) :
    s.lower.eval σ = s.eval σ := by
  cases s <;> rfl

/-- A simple value denotes what it evaluates to. -/
theorem Simple.denote_lower {p : PrimTy} (se : Simple C Γ p) (σ : EState C Γ) {v : Value}
    (h : se.eval σ = .ok v) : se.lower.denote σ = .prim v := by
  cases se <;> cases h <;> rfl

end Rules

/-! ## Formulas -/

/-- `p` after a typed run under `m`: `p` of the state it ends in,
`m.onTHalt` on a halt (both modalities accept `exhausted`, decision 15), and
no panic. -/
def _root_.Solidity.Modality.afterRunTR {α : Type} (m : Modality) (p : α → Prop) (r : TRes α) :
    Prop :=
  (match r with
    | .ok a => p a
    | .error e => m.onTHalt e) ∧ r ≠ .error .panic

/-- The state a modality's program, then its frames, end in. -/
def Prog.runFrames {Γ Γ₁ Γ₀ : Ctx} (σ : State C Γ) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) :
    TRes (State C Γ₀) := do
  let o ← Prog.run σ P
  let o' ← Frames.run o.st κ
  pure o'.st

/-- **Whether `φ` holds in the typed state `σ`.** -/
def holds : {Γ : Ctx} → State C Γ → Fml C Γ → Prop
  | _, _, .tt => True
  | _, σ, .eq a b => Theory.StValue.Equiv (a.denote σ.erase) (b.denote σ.erase)
  | _, σ, .defined t => ∃ x, t.eval σ.erase = .ok x
  | _, σ, .not φ => ¬ holds σ φ
  | _, σ, .and φ ψ => holds σ φ ∧ holds σ ψ
  | _, σ, .imp φ ψ => holds σ φ → holds σ ψ
  | _, σ, .upd m U φ =>
    m.afterC (fun τ => ∀ σ' : State C _, σ'.erase = τ → σ.H <+: σ'.H → holds σ' φ)
      (U.apply σ.erase)
  | _, σ, .modal m P κ φ => m.afterRunTR (holds · φ) (Prog.runFrames σ P κ)
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
def Valid (φ : Fml C []) : Prop := ∀ σ : State C [], holds σ φ

/-! ## A callee's and a loop's state, erased -/

theorem State.havoc_erase {Γ : Ctx} (σ : State C Γ) (st : Storage C) (nt : List (Int × Int)) :
    (σ.havoc st nt).erase = σ.erase.withGlob (σ.erase.glob.havoc st.erase nt) := rfl

theorem State.anon_erase {Γ : Ctx} (σ : State C Γ) (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C σ.H) :
    (σ.anon xs b).erase = σ.erase.anon xs fun x => LTy.TDenote.erase x.1 (b x) := by
  have key : ∀ (ys : List ((t : LTy) × Idx Γ t)) (e : TEnv C σ.H Γ),
      (σ.withEnv (ys.foldl (fun e x => TEnv.set x.2 (b x) e) e)).erase =
        ys.foldl (fun τ x => τ.setLocal x.2 (LTy.TDenote.erase x.1 (b x))) (σ.withEnv e).erase := by
    intro ys
    induction ys with
    | nil => intro e; rfl
    | cons x ys ih =>
      intro e
      rw [List.foldl_cons, List.foldl_cons, ih]
      exact congrArg (fun τ => List.foldl _ τ ys) (State.setLocal_erase (σ.withEnv e) x.2 (b x))
  exact key xs σ.env

theorem _root_.Solidity.Modality.afterC_imp {α : Type} {m : Modality} {p q : α → Prop}
    {r : Semantics.Res α} (h : m.afterC p r) (hpq : ∀ a, p a → q a) : m.afterC q r := by
  cases r with
  | ok a => exact hpq a h
  | error _ => exact h

end Solidity
