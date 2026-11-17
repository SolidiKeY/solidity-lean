import Solidity.Syntax.Elab.Arms

/-!
# A termination measure for the elaborator knot

The vocabulary in which a well-founded totalization of the `mutual` knot of
`Syntax/Elab/Stmt.lean` states its decrease, over the five recursive fields
that clause 2 of `Solidity.Goals.elabKernelTotal` (`ElabKernelInduction`)
names: `hoist`, `hoistStmt`, `elabStmtP`, `elabStmt1`, `elabStmtsP`.

* `ElabMeasure α`: one measure per field, of the input and the scope (the
  functions still inlinable, `ElabScope.funs`/`recs`), into a well-founded `α`.
* `ElabMeasure.cut μ a r`: `r` with each of the five fields failing at every
  call whose measure is not below `a`, the other fields kept.
* `ElabMeasure.Stable μ J m arm`: the arm at `x` gives the same result over
  `r` as over `cut μ (m x sc) r`, for every record `r` whose runs below the
  measure of `x` meet the guard `J`: the arm calls the five fields only below
  its own measure.  This is "the arm at `x` gives the same result for two
  records that agree below the measure of `x`", relativized to `J`.

The guard is needed.  With the trivial guard (`ElabPreds.top`) the shape
fails for every well-founded measure along one path
(`Solidity/Examples/ElabTotal/Measure.lean`, `rel_cycle_forT_blk`):
`elabStmtPWith` passes the statement `rc.hoistStmt` returns to `rc.elabStmt1`
(nested recursion), so over a record whose `hoistStmt` returns a `for` loop
with an initializer the arms call
`elabStmtP blk → elabStmt1 (for …) → elabStmtsP [blk] → elabStmtP blk` at one
scope.  Which guard makes the five arms stable is open: a candidate bounds
what `hoistStmt` and `hoist` return by their inputs, in the measure, and is
not established here.  `Solidity/Examples/ElabTotal/Measure.lean` shows that
clause 2 follows from guarded stability of the five arms and the guard's
preservation by them, for any guard.
-/

namespace Solidity

open Semantics

/-- No element of a well-founded relation lies on a cycle of three. -/
theorem rel_cycle3 {α : Type} [WellFoundedRelation α] {a b c : α}
    (h1 : WellFoundedRelation.rel a b) (h2 : WellFoundedRelation.rel b c)
    (h3 : WellFoundedRelation.rel c a) : False :=
  WellFounded.induction (C := fun a => ∀ b c, WellFoundedRelation.rel a b →
      WellFoundedRelation.rel b c → WellFoundedRelation.rel c a → False)
    WellFoundedRelation.wf a (fun _ ih b c h1 h2 h3 => ih c h3 _ b h3 h1 h2) b c h1 h2 h3

/-- What a run of each of the five fields may be asked to meet: the shapes of
`ElabKernelInduction`'s predicates. -/
structure ElabPreds (C : Contract) where
  hoist : RawExpr → ElabScope → ECtx × Nat → SProg C × RawExpr → ECtx × Nat → Prop
  hoistStmt : RawStmt → ElabScope → ECtx × Nat → SProg C × RawStmt → ECtx × Nat → Prop
  elabStmtP : RawStmt → ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop
  elabStmt1 : RawStmt → ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop
  elabStmtsP : List RawStmt → ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop

/-- The trivial guard. -/
def ElabPreds.top (C : Contract) : ElabPreds C :=
  ⟨fun _ _ _ _ _ => True, fun _ _ _ _ _ => True, fun _ _ _ _ _ => True,
    fun _ _ _ _ _ => True, fun _ _ _ _ _ => True⟩

/-- Every successful run of `f x` from the scope `sc` meets `Q`. -/
def RunsMeet {β γ : Type} (Q : β → ElabScope → ECtx × Nat → γ → ECtx × Nat → Prop)
    (f : β → ElabM γ) (x : β) (sc : ElabScope) : Prop :=
  ∀ st b st' m m', (((f x).run sc).run st).run m = .ok ((b, st'), m') → Q x sc st b st'

/-- One measure per recursive field: of the input and the scope. -/
structure ElabMeasure (α : Type) where
  hoist : RawExpr → ElabScope → α
  hoistStmt : RawStmt → ElabScope → α
  elabStmtP : RawStmt → ElabScope → α
  elabStmt1 : RawStmt → ElabScope → α
  elabStmtsP : List RawStmt → ElabScope → α

namespace ElabMeasure

variable {α : Type} [WellFoundedRelation α]

open Classical in
/-- `f` below `a`: a call whose measure is not below `a` fails. -/
noncomputable def cutF {β γ : Type} (m : β → ElabScope → α) (a : α) (f : β → ElabM γ) :
    β → ElabM γ :=
  fun x sc => if WellFoundedRelation.rel (m x sc) a then (f x).run sc else (throw "" : ElabM γ).run sc

open Classical in
theorem cutF_run {β γ : Type} (m : β → ElabScope → α) (a : α) (f : β → ElabM γ) (x : β)
    (sc : ElabScope) :
    (cutF m a f x).run sc =
      if WellFoundedRelation.rel (m x sc) a then (f x).run sc else (throw "" : ElabM γ).run sc :=
  rfl

/-- The cut meets what `f` meets below `a`, everywhere. -/
theorem cutF_meets {β γ : Type} {m : β → ElabScope → α} {a : α} {f : β → ElabM γ}
    {Q : β → ElabScope → ECtx × Nat → γ → ECtx × Nat → Prop}
    (h : ∀ x sc, WellFoundedRelation.rel (m x sc) a → RunsMeet Q f x sc) :
    ∀ x sc, RunsMeet Q (cutF m a f) x sc := by
  intro x sc st b st' m0 m1 hrun
  by_cases hlt : WellFoundedRelation.rel (m x sc) a
  · rw [cutF_run, if_pos hlt] at hrun
    exact h x sc hlt st b st' m0 m1 hrun
  · rw [cutF_run, if_neg hlt] at hrun
    cases hrun

/-- `r`'s five recursive fields cut below `a`; its other fields kept. -/
noncomputable def cut {C : Contract} (μ : ElabMeasure α) (a : α) (r : ElabRec C) : ElabRec C :=
  { r with
    hoist := cutF μ.hoist a r.hoist
    hoistStmt := cutF μ.hoistStmt a r.hoistStmt
    elabStmtP := cutF μ.elabStmtP a r.elabStmtP
    elabStmt1 := cutF μ.elabStmt1 a r.elabStmt1
    elabStmtsP := cutF μ.elabStmtsP a r.elabStmtsP }

/-- The runs of `r`'s five fields below `a` meet `J`. -/
def MeetsBelow {C : Contract} (μ : ElabMeasure α) (J : ElabPreds C) (a : α) (r : ElabRec C) :
    Prop :=
  (∀ x sc, WellFoundedRelation.rel (μ.hoist x sc) a → RunsMeet J.hoist r.hoist x sc) ∧
  (∀ x sc, WellFoundedRelation.rel (μ.hoistStmt x sc) a → RunsMeet J.hoistStmt r.hoistStmt x sc) ∧
  (∀ x sc, WellFoundedRelation.rel (μ.elabStmtP x sc) a → RunsMeet J.elabStmtP r.elabStmtP x sc) ∧
  (∀ x sc, WellFoundedRelation.rel (μ.elabStmt1 x sc) a → RunsMeet J.elabStmt1 r.elabStmt1 x sc) ∧
  (∀ x sc, WellFoundedRelation.rel (μ.elabStmtsP x sc) a → RunsMeet J.elabStmtsP r.elabStmtsP x sc)

/-- **The arm's decrease**: at `x`, `arm` gives over `r` what it gives over
`r` cut below the measure of `x`, for every `r` whose runs below meet `J`. -/
def Stable {C : Contract} {β γ : Type} (μ : ElabMeasure α) (J : ElabPreds C)
    (m : β → ElabScope → α) (arm : ElabRec C → β → ElabM γ) : Prop :=
  ∀ (r : ElabRec C) x sc, MeetsBelow μ J (m x sc) r →
    (arm (cut μ (m x sc) r) x).run sc = (arm r x).run sc

/-- The block's `elabStmtsP`, over the record (`Goals.elabStmtsStep`). -/
def stmtsArm {C : Contract} (rc : ElabRec C) : List RawStmt → ElabM (SProg C)
  | [] => pure []
  | s :: ss => do
    let P ← rc.elabStmtP s
    let Q ← rc.elabStmtsP ss
    pure (P ++ Q)

/-- **The measure decreases on `elabStmtsP`'s arm**: it calls `elabStmtP` at
the head and `elabStmtsP` at the tail, both at its own scope. -/
theorem stmtsArm_stable {C : Contract} (μ : ElabMeasure α) (J : ElabPreds C)
    (hhead : ∀ s ss sc, WellFoundedRelation.rel (μ.elabStmtP s sc) (μ.elabStmtsP (s :: ss) sc))
    (htail : ∀ s ss sc, WellFoundedRelation.rel (μ.elabStmtsP ss sc) (μ.elabStmtsP (s :: ss) sc)) :
    Stable μ J μ.elabStmtsP (stmtsArm (C := C)) := by
  intro r x sc _
  cases x with
  | nil => rfl
  | cons s ss =>
    have e1 : ((cut μ (μ.elabStmtsP (s :: ss) sc) r).elabStmtP s).run sc =
        (r.elabStmtP s).run sc := by
      exact (cutF_run ..).trans (if_pos (hhead s ss sc))
    have e2 : ((cut μ (μ.elabStmtsP (s :: ss) sc) r).elabStmtsP ss).run sc =
        (r.elabStmtsP ss).run sc := by
      exact (cutF_run ..).trans (if_pos (htail s ss sc))
    simp only [stmtsArm, ReaderT.run, bind, ReaderT.bind] at e1 e2 ⊢
    rw [e1]
    funext st m
    simp only [e2]

end ElabMeasure

end Solidity
