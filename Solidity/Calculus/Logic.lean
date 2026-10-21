import Solidity.Calculus.Lands

/-!
# What a scoped formula means

The scoped formulas of `Calculus/Fml.lean` read over the typed state
(`State`, `Semantics/State.lean`) and the typed run (`Prog.run`,
`Frames.run`): `holds`, `Valid`.

* A term in an equation is read in the typed Theory (`Tm.denote`,
  `Calculus/Lands.lean`, KeY's total model), a typed value as its
  observations (`SVal.obs`), equal by `=`, total as KeY's `=` is: there
  is no definedness test.  What a program reads where it may revert is
  evaluated by the program (a rule captures it in a local), not by a
  formula.  `wt(s)` is a predicate, KeY's `wellFormed(heap)`, the
  interpreter's test of the storage `s` evaluates to (`Storage.wtB`).
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
  | _, σ, .eq a b => a.denote σ = b.denote σ
  | _, σ, .wellFormed s => ∃ st, s.eval σ = some st ∧ st.wtB = true
  | _, σ, .not φ => ¬ holds σ φ
  | _, σ, .and φ ψ => holds σ φ ∧ holds σ ψ
  | _, σ, .imp φ ψ => holds σ φ → holds σ ψ
  | _, σ, .upd m U φ => U.afterT m σ (holds · φ)
  | _, σ, .modal m P κ φ => m.afterRunTR (holds · φ) (Prog.runFrames σ P κ)
  | _, σ, .havoc φ => ∀ st nt, holds (σ.havoc st nt) φ
  | _, σ, .all _ p φ => ∀ v : p.Denote, holds (σ.push (t := .val p) v) φ
  | _, σ, .bind m _ t φ => m.forallB fun v : t.TDenote C σ.H => holds (σ.push v) φ
  | _, σ, .anon xs φ => ∀ b, holds (σ.anon xs b) φ
  | _, σ, .allocAll _ R φ => ∀ o : MObj σ.H R,
      holds ((σ.alloc o).1.push (t := .mem R) (some (σ.alloc o).2)) φ

/-- An equation of `holds`, read by the typed readers. -/
theorem holds_eq {Γ : Ctx} {p : PrimTy} (σ : State C Γ) (a b : Tm C Γ (.val p)) :
    holds σ (.eq a b) ↔ a.denote σ = b.denote σ := Iff.rfl

/-- `wt(s)` of `holds`: the storage `s` evaluates to passes the test. -/
theorem holds_wellFormed {Γ : Ctx} (σ : State C Γ) (s : Tm C Γ .st) :
    holds σ (.wellFormed s) ↔ ∃ st, s.eval σ = some st ∧ st.wtB = true := Iff.rfl

/-- `wt(s)` holds exactly where the symbol `wt(s)` returns. -/
theorem holds_wellFormed_eval {Γ : Ctx} (σ : State C Γ) (s : Tm C Γ .st) :
    holds σ (.wellFormed s) ↔ (Tm.app1 .wt s).eval σ ≠ none := by
  show _ ↔ (s.eval σ).bind Storage.wtT ≠ none
  rw [holds_wellFormed]
  cases s.eval σ with
  | none => simp only [reduceCtorEq, false_and, exists_false, Option.bind_none, ne_eq,
      not_true_eq_false]
  | some st =>
    simp only [Option.some.injEq, exists_eq_left', Option.bind_some, Storage.wtT, ne_eq]
    cases st.wtB <;> simp only [if_true, Bool.false_eq_true, if_false, reduceCtorEq,
      not_true_eq_false, not_false_eq_true]

/-- An equation of a value local and a literal holds where the local holds
the literal: both sides return. -/
theorem holds_eq_pvV_lit {Γ : Ctx} {p : PrimTy} (σ : State C Γ) (i : Idx Γ (.val p))
    (v : p.Denote) :
    holds σ (.eq (.pvV i) (.app0 (.lit v))) ↔ TEnv.get i σ.env = v :=
  ⟨fun h => Option.some.inj h, fun h => congrArg some h⟩

/-- An equation of two terms that return holds where they return one value
(`Tm.denote_eval`). -/
theorem holds_eq_of_eval {Γ : Ctx} {p : PrimTy} {σ : State C Γ} {a b : Tm C Γ (.val p)}
    {x y : p.Denote} (ha : a.eval σ = some x) (hb : b.eval σ = some y) :
    holds σ (.eq a b) ↔ x = y := by
  rw [holds_eq, Tm.denote_eval σ a x ha, Tm.denote_eval σ b y hb, Option.some.injEq]

/-- Every local's type has a value in every typed state: an alias and a
memory local unset among them (decision 17'). -/
theorem LTy.tdenote_nonempty {H : HTy} : (t : LTy) → Nonempty (t.TDenote C H)
  | .val p => ⟨PrimTy.dflt p⟩
  | .alias _ => ⟨none⟩
  | .mem _ => ⟨none⟩
  | .old => ⟨Storage.init C⟩
  | .oldNet => ⟨[]⟩
  | .kint => ⟨(0 : Int)⟩

/-- Valid over the typed states: true in every typed state of the empty
context. -/
def Valid (φ : Fml C []) : Prop := ∀ σ : State C [], holds σ φ

end Solidity
