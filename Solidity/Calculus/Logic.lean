import Solidity.Calculus.Lands

/-!
# What a scoped formula means

The scoped formulas of `Calculus/Fml.lean` read over the typed state
(`State`, `Semantics/State.lean`) and the typed run (`Prog.run`,
`Frames.run`): `holds`, `Valid`.

* A term in an equation or a definedness test is read on the typed state
  (`Tm.denoteT`, `Tm.evalT`, `Calculus/Lands.lean`): a local by its
  position, erased at its type (`State.getE`), a symbol on the global part
  erased (`State.globE`); its symbols are untyped (decision 83).
* An update is parallel (every right-hand side read in the state it is
  applied in) and leaves the context `Δ` its type says: a declaration
  pushes, a pop drops a suffix, a `drop` thins.  What follows it is read in
  every typed state it lands on (`Upd.afterT`, `Upd.Lands`, W9.7.1): the
  global part it computes, each local holding what it left there
  (`Upd.held`), read on the typed state it is applied in, and a heap typing
  that extends that state's, as a typed run's does (`Out.ext`).  Those are
  the typed states that erase to what `Upd.apply` computes on the erasure
  (`Upd.lands_iff`), so the clause is also read there (`holds_upd_erased`,
  what the layers above read until W9.7.2 ports them).  The rules' updates
  land on the state the statement's typed run ends in; an update that
  lands on no typed state (a value of another type) says nothing.
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

The rules' soundness (`Calculus/Sound*.lean`) relates the typed run to
`Update.lean`'s terms directly: a statement's typed step agrees with its
update applied to the erasure (`TRes.Agrees`, `Calculus/SoundArms.lean`),
each lowered expression's term reading what the typed evaluator returns
(`Calculus/LowerRun.lean`); no program evaluator of the erasure is between.
-/

namespace Solidity
open Semantics (Value SVal MVal Seg Halt Res lookupBy setBy allocDefault applyUnOp)
open Solidity (evalBinop unopCheck)
open Theory Theory.StValue
open Solidity (Srt Op0 Op1 Op2 Op3 Modality IntOp)

variable {C : Contract}

/-- The locals `xs` set as `b` says: a loop body's frame anonymised. -/
def EState.anon {Γ : Ctx} (σ : EState C Γ) (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.Denote C) : EState C Γ :=
  xs.foldl (fun τ x => τ.setLocal x.2 (b x)) σ

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
  | _, σ, .eq a b => Theory.StValue.Equiv (a.denoteT σ) (b.denoteT σ)
  | _, σ, .defined t => ∃ x, t.evalT σ = .ok x
  | _, σ, .not φ => ¬ holds σ φ
  | _, σ, .and φ ψ => holds σ φ ∧ holds σ ψ
  | _, σ, .imp φ ψ => holds σ φ → holds σ ψ
  | _, σ, .upd m U φ => U.afterT m σ (holds · φ)
  | _, σ, .modal m P κ φ => m.afterRunTR (holds · φ) (Prog.runFrames σ P κ)
  | _, σ, .havoc φ => ∀ st nt, holds (σ.havoc st nt) φ
  | _, σ, .all _ p φ => ∀ v : p.Denote, holds (σ.push (t := .val p) v) φ
  | _, σ, .bind m _ t φ => m.forallB fun v : t.TDenote C σ.H => holds (σ.push v) φ
  | _, σ, .anon xs φ => ∀ b, holds (σ.anon xs b) φ

/-- `holds`' update clause, read on the erasure (`Upd.afterT_iff`): what
the layers above `Logic` unfolded before W9.7.1. -/
theorem holds_upd_erased {Γ Δ : Ctx} (σ : State C Γ) (m : Modality) (U : Upd C Γ Δ)
    (φ : Fml C Δ) :
    holds σ (.upd m U φ) ↔
      m.afterC (fun τ => ∀ σ' : State C Δ, σ'.erase = τ → σ.H <+: σ'.H → holds σ' φ)
        (U.apply σ.erase) :=
  Upd.afterT_iff m σ U _

/-- `holds`' equation clause, read on the erasure (`Tm.denoteT_eq`): what
the layers above `Logic` unfolded before W9.7.2. -/
theorem holds_eq_erased {Γ : Ctx} (σ : State C Γ) (a b : Tm C Γ .val) :
    holds σ (.eq a b) ↔ Theory.StValue.Equiv (a.denote σ.erase) (b.denote σ.erase) := by
  show Theory.StValue.Equiv (a.denoteT σ) (b.denoteT σ) ↔ _
  rw [Tm.denoteT_eq, Tm.denoteT_eq]

/-- `holds`' definedness clause, read on the erasure (`Tm.evalT_eq`). -/
theorem holds_defined_erased {Γ : Ctx} (σ : State C Γ) (t : Tm C Γ .val) :
    holds σ (.defined t) ↔ ∃ x, t.eval σ.erase = .ok x := by
  show (∃ x, t.evalT σ = .ok x) ↔ _
  rw [Tm.evalT_eq]

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
