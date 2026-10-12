import Solidity.Calculus.Lands

/-!
# What a scoped formula means

The scoped formulas of `Calculus/Fml.lean` read over the typed state
(`State`, `Semantics/State.lean`) and the typed run (`Prog.run`,
`Frames.run`): `holds`, `Valid`.

* A term in an equation is read in the Theory (`Tm.denote`,
  `Calculus/Lands.lean`, KeY's total model, the W9.8.0 decision), a typed
  value through its abstraction (`SVal.absT`); a definedness test reads it on
  the typed state (`Tm.eval`, `Calculus/TermEval.lean`): `none` where it
  reverts.
* An update is parallel (every right-hand side read in the state it is
  applied in) and leaves the context `Δ` its type says: a declaration
  pushes, a pop drops a suffix, a `drop` thins.  What follows it is read in
  every typed state it lands on (`Upd.afterT`, `Upd.Lands`, W9.7.1 and
  W9.8.3): the typed global part it computes, whose heap typing extends the
  state's it is applied in (`GlobT`), each local holding what it left there
  (`Upd.held`), read on the typed state it is applied in.  The
  closer and the decision procedure compute it (`Upd.applyV`,
  `Upd.afterT_applyV`).  The rules' updates land on the state the
  statement's typed run ends in; an update that lands on no typed state (a
  value of another type) says nothing.
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

The rules' soundness (`Calculus/Sound*.lean`) relates the typed run to the
terms directly: a statement's typed step agrees with what its update
computes (`TRes.AgreesO` against `Upd.applyV`, `Calculus/SoundArms.lean`),
each lowered expression's term reading what the typed evaluator returns
(`Calculus/LowerRun.lean`).
-/

namespace Solidity
open Theory Theory.StValue
open Solidity (Srt Modality)

variable {C : Contract}

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
  | _, σ, .eq a b => Theory.StValue.Equiv (a.denote σ) (b.denote σ)
  | _, σ, .defined t => t.eval σ ≠ none
  | _, σ, .not φ => ¬ holds σ φ
  | _, σ, .and φ ψ => holds σ φ ∧ holds σ ψ
  | _, σ, .imp φ ψ => holds σ φ → holds σ ψ
  | _, σ, .upd m U φ => U.afterT m σ (holds · φ)
  | _, σ, .modal m P κ φ => m.afterRunTR (holds · φ) (Prog.runFrames σ P κ)
  | _, σ, .havoc φ => ∀ st nt, holds (σ.havoc st nt) φ
  | _, σ, .all _ p φ => ∀ v : p.Denote, holds (σ.push (t := .val p) v) φ
  | _, σ, .bind m _ t φ => m.forallB fun v : t.TDenote C σ.H => holds (σ.push v) φ
  | _, σ, .anon xs φ => ∀ b, holds (σ.anon xs b) φ

/-- An equation of `holds`, read by the typed readers. -/
theorem holds_eq {Γ : Ctx} {p : PrimTy} (σ : State C Γ) (a b : Tm C Γ (.val p)) :
    holds σ (.eq a b) ↔ Theory.StValue.Equiv (a.denote σ) (b.denote σ) := Iff.rfl

/-- A `defined` of `holds`, read by the typed readers. -/
theorem holds_defined {Γ : Ctx} {p : PrimTy} (σ : State C Γ) (t : Tm C Γ (.val p)) :
    holds σ (.defined t) ↔ t.eval σ ≠ none := Iff.rfl

/-- An equation of two defined values holds where they read alike. -/
theorem holds_eqD {Γ : Ctx} {p : PrimTy} (σ : State C Γ) (a b : Tm C Γ (.val p)) :
    holds σ (.eqD a b) ↔ ∃ x, a.eval σ = some x ∧ b.eval σ = some x := by
  constructor
  · rintro ⟨ha, hb, he⟩
    rw [holds_defined] at ha hb
    rw [holds_eq] at he
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 ha
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hb
    have ex : a.denote σ = .prim (PrimTy.erase x) := Tm.denote_eval σ a x hx
    have ey : b.denote σ = .prim (PrimTy.erase y) := Tm.denote_eval σ b y hy
    rw [ex, ey, StValue.Equiv.prim_iff] at he
    obtain rfl := PrimTy.erase_injective (StValue.prim.inj he)
    exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    refine ⟨(holds_defined σ a).2 (by rw [hx]; exact nofun),
      (holds_defined σ b).2 (by rw [hy]; exact nofun), ?_⟩
    show StValue.Equiv _ _
    rw [Tm.denote_eval σ a x hx, Tm.denote_eval σ b x hy]
    exact StValue.Equiv.refl _

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

end Solidity
