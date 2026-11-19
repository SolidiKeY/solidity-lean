import Solidity.Goals.ElabTotal
import Solidity.Syntax.Elab.Measure

/-!
# Checks: the elaborator measure

Two results about clause 2 of `Solidity.Goals.elabKernelTotal`
(`ElabKernelInduction`) and the measure vocabulary of
`Solidity/Syntax/Elab/Measure.lean`.

* **Clause 2 is an instance of the arms' guarded decrease**
  (`elabKernelInduction_of_stable`): for any record satisfying the knot's
  equations (clause 1, `ElabKernelFix`), a well-founded measure under which the
  five arms are `Stable` relative to a guard `J` that the arms keep gives the
  induction principle, by well-founded induction over the measure, applying
  its hypothesis to the record cut below each level (`ElabMeasure.cut`).
* **Counterexample: with no guard, no measure decreases** (the `#guard`s
  below).  `elabStmtPWith` passes `rc.hoistStmt`'s output to `rc.elabStmt1`
  (nested recursion, `Syntax/Elab/Arms.lean`, `elabStmtPWith`:
  `let (P, s) ← hoistStmt s` then `elabStmt1 s`), so over a record whose
  `hoistStmt` returns `t = for (; ; ) { e; }` (`forT`, an initializer `[e]`),
  the recursion path is, all at the scope `sc0`:

      elabStmtP blk              -- elabStmtPWith, its hoistStmt returning `forT`
        → elabStmt1 forT          -- elabStmt1With, a loop: `lowerLoops none [forT]`
        → elabStmtsP [blk]        -- elabStmtsStep, at its head
        → elabStmtP blk

  where `blk = { e; loop (true) {} }` is `lowerLoops none [forT]`'s block.
  Each arrow is a call the arm makes through its record whose result is the
  arm's result (the spies below throw, and the arm throws what they throw), so
  `Stable μ (ElabPreds.top C)` for the three arms needs
  `μ.elabStmt1 forT sc0 < μ.elabStmtP blk sc0 < μ.elabStmtsP [blk] sc0 <
  μ.elabStmt1 forT sc0`, a cycle (`rel_cycle_forT_blk`).  The last decrease
  is proved from `Stable` (`stmtsStep_head_lt`); the first two are shown by
  evaluation only.  The spies report the scope's
  inlining state (`funs`, `recs`, `inlined`, `top`), the same at every call.
-/

namespace Solidity.Examples.ElabTotalMeasure

open Solidity Semantics Goals ElabMeasure

section Induction

variable [FreshNames] {C : Contract} {α : Type} [WellFoundedRelation α]

omit [FreshNames] in
theorem elabSat_iff {β γ : Type} {Q : β → ElabScope → ECtx × Nat → γ → ECtx × Nat → Prop}
    {f : β → ElabM γ} : ElabSat Q f ↔ ∀ x sc, RunsMeet Q f x sc := by
  constructor
  · intro h x sc st b st' m m' hr
    exact h x sc st b st' ⟨m, m', hr⟩
  · intro h x sc st b st' ⟨m, m', hr⟩
    exact h x sc st b st' m m' hr

omit [FreshNames] in
theorem elabStmtsStep_eq (r : ElabRec C) : elabStmtsStep C r = stmtsArm r := by
  funext ss
  cases ss <;> rfl

/-- The five arms decrease under `μ`, relative to the guard `J`. -/
def ArmsStable (μ : ElabMeasure α) (J : ElabPreds C) : Prop :=
  Stable μ J μ.hoist (hoistWith C) ∧ Stable μ J μ.hoistStmt (hoistStmtWith C) ∧
  Stable μ J μ.elabStmtP (elabStmtPWith C) ∧ Stable μ J μ.elabStmt1 (elabStmt1With C) ∧
  Stable μ J μ.elabStmtsP (elabStmtsStep C)

/-- The arms keep the guard: `ElabKernelInduction`'s hypothesis at `J`. -/
def GuardKept (J : ElabPreds C) : Prop :=
  ∀ r : ElabRec C, ElabSat J.hoist r.hoist → ElabSat J.hoistStmt r.hoistStmt →
    ElabSat J.elabStmtP r.elabStmtP → ElabSat J.elabStmt1 r.elabStmt1 →
    ElabSat J.elabStmtsP r.elabStmtsP →
    ElabSat J.hoist (hoistWith C r) ∧ ElabSat J.hoistStmt (hoistStmtWith C r) ∧
      ElabSat J.elabStmtP (elabStmtPWith C r) ∧ ElabSat J.elabStmt1 (elabStmt1With C r) ∧
      ElabSat J.elabStmtsP (elabStmtsStep C r)

omit [FreshNames] [WellFoundedRelation α] in
/-- One field at one level: its runs are its arm's over the cut record. -/
theorem field_meets {β γ : Type} {m : β → ElabScope → α} {a : α} {f : β → ElabM γ}
    {arm : ElabRec C → β → ElabM γ} {r' rc : ElabRec C}
    {Q J : β → ElabScope → ECtx × Nat → γ → ECtx × Nat → Prop}
    (hf : f = arm rc) (hst : ∀ x sc, m x sc = a → (arm r' x).run sc = (arm rc x).run sc)
    (hQ : ElabSat Q (arm r')) (hJ : ElabSat J (arm r')) :
    ∀ x sc, m x sc = a →
      RunsMeet (fun x sc st b st' => Q x sc st b st' ∧ J x sc st b st') f x sc := by
  intro x sc hx st b st' m0 m1 hr
  subst hf
  rw [← hst x sc hx] at hr
  exact ⟨hQ x sc st b st' ⟨m0, m1, hr⟩, hJ x sc st b st' ⟨m0, m1, hr⟩⟩

omit [FreshNames] in
/-- A `Stable` arm at the level `a`, over a record whose runs below `a` meet `J`. -/
theorem stable_at {β γ : Type} {μ : ElabMeasure α} {J : ElabPreds C} {m : β → ElabScope → α}
    {arm : ElabRec C → β → ElabM γ} {a : α} {rc : ElabRec C} (h : Stable μ J m arm)
    (hb : MeetsBelow μ J a rc) :
    ∀ x sc, m x sc = a → (arm (cut μ a rc) x).run sc = (arm rc x).run sc := by
  intro x sc hx
  subst hx
  exact h rc x sc hb

/-- **Clause 2 from the arms' guarded decrease.** -/
theorem elabKernelInduction_of_stable (μ : ElabMeasure α) (J : ElabPreds C) (rc : ElabRec C)
    (hfix : ElabKernelFix C rc) (hst : ArmsStable μ J) (hJ : GuardKept J) :
    ElabKernelInduction C rc := by
  intro QH QS QP Q1 QL hQ
  obtain ⟨hnil, hcons, hP, h1, hS, hH⟩ := hfix
  have hL : rc.elabStmtsP = elabStmtsStep C rc := by
    funext ss
    cases ss with
    | nil => exact hnil
    | cons s ss => exact hcons s ss
  let K : ElabPreds C :=
    ⟨fun x sc st b st' => QH x sc st b st' ∧ J.hoist x sc st b st',
     fun x sc st b st' => QS x sc st b st' ∧ J.hoistStmt x sc st b st',
     fun x sc st b st' => QP x sc st b st' ∧ J.elabStmtP x sc st b st',
     fun x sc st b st' => Q1 x sc st b st' ∧ J.elabStmt1 x sc st b st',
     fun x sc st b st' => QL x sc st b st' ∧ J.elabStmtsP x sc st b st'⟩
  have key : ∀ a : α,
      (∀ x sc, μ.hoist x sc = a → RunsMeet K.hoist rc.hoist x sc) ∧
      (∀ x sc, μ.hoistStmt x sc = a → RunsMeet K.hoistStmt rc.hoistStmt x sc) ∧
      (∀ x sc, μ.elabStmtP x sc = a → RunsMeet K.elabStmtP rc.elabStmtP x sc) ∧
      (∀ x sc, μ.elabStmt1 x sc = a → RunsMeet K.elabStmt1 rc.elabStmt1 x sc) ∧
      (∀ x sc, μ.elabStmtsP x sc = a → RunsMeet K.elabStmtsP rc.elabStmtsP x sc) := by
    intro a
    refine WellFounded.induction (C := fun a =>
      (∀ x sc, μ.hoist x sc = a → RunsMeet K.hoist rc.hoist x sc) ∧
      (∀ x sc, μ.hoistStmt x sc = a → RunsMeet K.hoistStmt rc.hoistStmt x sc) ∧
      (∀ x sc, μ.elabStmtP x sc = a → RunsMeet K.elabStmtP rc.elabStmtP x sc) ∧
      (∀ x sc, μ.elabStmt1 x sc = a → RunsMeet K.elabStmt1 rc.elabStmt1 x sc) ∧
      (∀ x sc, μ.elabStmtsP x sc = a → RunsMeet K.elabStmtsP rc.elabStmtsP x sc))
      WellFoundedRelation.wf a ?_
    intro a ih
    have bK : MeetsBelow μ K a rc :=
      ⟨fun x sc h => (ih _ h).1 x sc rfl, fun x sc h => (ih _ h).2.1 x sc rfl,
       fun x sc h => (ih _ h).2.2.1 x sc rfl, fun x sc h => (ih _ h).2.2.2.1 x sc rfl,
       fun x sc h => (ih _ h).2.2.2.2 x sc rfl⟩
    have bJ : MeetsBelow μ J a rc :=
      ⟨fun x sc h st b st' m m' hr => (bK.1 x sc h st b st' m m' hr).2,
       fun x sc h st b st' m m' hr => (bK.2.1 x sc h st b st' m m' hr).2,
       fun x sc h st b st' m m' hr => (bK.2.2.1 x sc h st b st' m m' hr).2,
       fun x sc h st b st' m m' hr => (bK.2.2.2.1 x sc h st b st' m m' hr).2,
       fun x sc h st b st' m m' hr => (bK.2.2.2.2 x sc h st b st' m m' hr).2⟩
    have cH := cutF_meets bK.1
    have cS := cutF_meets bK.2.1
    have cP := cutF_meets bK.2.2.1
    have c1 := cutF_meets bK.2.2.2.1
    have cL := cutF_meets bK.2.2.2.2
    let r' := cut μ a rc
    obtain ⟨qH, qS, qP, q1, qL⟩ := hQ r'
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cH x sc st b st' m m' hr).1)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cS x sc st b st' m m' hr).1)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cP x sc st b st' m m' hr).1)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (c1 x sc st b st' m m' hr).1)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cL x sc st b st' m m' hr).1)
    obtain ⟨jH, jS, jP, j1, jL⟩ := hJ r'
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cH x sc st b st' m m' hr).2)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cS x sc st b st' m m' hr).2)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cP x sc st b st' m m' hr).2)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (c1 x sc st b st' m m' hr).2)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cL x sc st b st' m m' hr).2)
    exact ⟨field_meets hH (stable_at hst.1 bJ) qH jH,
      field_meets hS (stable_at hst.2.1 bJ) qS jS,
      field_meets hP (stable_at hst.2.2.1 bJ) qP jP,
      field_meets h1 (stable_at hst.2.2.2.1 bJ) q1 j1,
      field_meets hL (stable_at hst.2.2.2.2 bJ) qL jL⟩
  exact ⟨elabSat_iff.2 fun x sc st b st' m m' hr => ((key _).1 x sc rfl st b st' m m' hr).1,
    elabSat_iff.2 fun x sc st b st' m m' hr => ((key _).2.1 x sc rfl st b st' m m' hr).1,
    elabSat_iff.2 fun x sc st b st' m m' hr => ((key _).2.2.1 x sc rfl st b st' m m' hr).1,
    elabSat_iff.2 fun x sc st b st' m m' hr => ((key _).2.2.2.1 x sc rfl st b st' m m' hr).1,
    elabSat_iff.2 fun x sc st b st' m m' hr => ((key _).2.2.2.2 x sc rfl st b st' m m' hr).1⟩

end Induction

section Counterexample

/-- A contract with nothing declared. -/
def C0 : Contract := { vars := [] }

/-- A branch's scope: no function inlinable, none recursing, nothing inlined. -/
def sc0 : ElabScope := { funs := [], top := false }

/-- `e;`, a statement with nothing to elaborate. -/
def eS : RawStmt := .eval []

/-- `for (e; ; ) { }`: a loop with an initializer. -/
def forT : RawStmt := .forLoop {} [eS] none [] []

/-- `{ e; loop (true) { } }`: `forT`, lowered. -/
def blk : RawStmt := .block [eS, .loop {} (.bool true) []]

/-- The spike's two statements have equal control weight: weight equality
alone cannot distinguish the loop from its lowered block. -/
example : CalleeKernel.stmtWeight forT = CalleeKernel.stmtWeight blk := rfl

/-- Rewriting only a loop's expressions cannot produce the spike's block,
even when the callback may fail or return arbitrary expressions. -/
example (f : RawExpr → Except String RawExpr) : forT.mapExprsM f ≠ .ok blk := by
  intro h
  have he := RawStmt.mapExprsM_control f forT
  rw [h] at he
  cases he

/-- An assignment cannot acquire the loop initializer used by the spy below,
even if its expression callback returns arbitrary expressions and programs. -/
example [FreshNames] (hoist : RawExpr → ElabM (SProg C0 × RawExpr))
    (l r : RawExpr) (sc : ElabScope) (st st' : ECtx × Nat) (m m' : CallMemo)
    (P : SProg C0) :
    (((hoistAssignWith C0 hoist l r).run sc).run st).run m ≠
      .ok (((P, forT), st'), m') := by
  intro h
  obtain ⟨l', r', he⟩ := hoistAssignWith_shape C0 hoist l r sc st st' m m' (P, forT) h
  cases he

/-- What bounds inlining at a call: the scope's functions, recursive frames and
inlined calls. -/
def scopeTag (sc : ElabScope) : String :=
  s!"funs={sc.funs.length} recs={sc.recs.length} inlined={sc.inlined} top={sc.top}"

/-- A field that fails with its input and the scope it is called at. -/
def spy {β γ : Type} [Repr β] (tag : String) : β → ElabM γ :=
  fun x => do throw s!"{tag} {reprStr x} @ {scopeTag (← read)}"

/-- The error an elaboration from `sc0` ends with (`ok` for none). -/
def errOf {γ : Type} (x : ElabM γ) : String :=
  match x.runFrom' sc0 ([], 0) with
  | .ok _ => "ok"
  | .error e => e

-- `lowerLoops none [forT] = [blk]`.
#guard match (lowerLoops none [forT]).runFrom' sc0 ([], 0) with
  | .ok ss => reprStr ss == reprStr [blk]
  | .error _ => false

/-- The record whose `hoistStmt` returns `forT`, `elabStmt1` a spy. -/
def recA : ElabRec C0 :=
  { elabRec C0 () with hoistStmt := fun _ => pure ([], forT), elabStmt1 := spy "elabStmt1" }

-- (1) `elabStmtPWith` at `blk` calls `elabStmt1` at `forT`, at `sc0`.
#guard errOf (elabStmtPWith C0 recA blk) == s!"elabStmt1 {reprStr forT} @ {scopeTag sc0}"

-- … and its result is that call's: with `elabStmt1` failing silently, so
-- does the arm.  (A `cut` of `recA` may also cut `hoistStmt`, which fails
-- with the same `""`.)
#guard errOf (elabStmtPWith C0 { recA with elabStmt1 := fun _ => throw "" } blk) == ""

-- (2) `elabStmt1With` at `forT` calls `elabStmtsP` at `[blk]`, at `sc0`.
#guard errOf (elabStmt1With C0 { elabRec C0 () with elabStmtsP := spy "elabStmtsP" } forT) ==
  s!"elabStmtsP {reprStr [blk]} @ {scopeTag sc0}"

#guard errOf (elabStmt1With C0 { elabRec C0 () with elabStmtsP := fun _ => throw "" } forT) == ""

-- (3) `elabStmtsStep` at `[blk]` calls `elabStmtP` at `blk`, at `sc0`: the
-- cycle is closed.
#guard errOf (elabStmtsStep C0 { elabRec C0 () with elabStmtP := spy "elabStmtP" } [blk]) ==
  s!"elabStmtP {reprStr blk} @ {scopeTag sc0}"

#guard errOf (elabStmtsStep C0 { elabRec C0 () with elabStmtP := fun _ => throw "" } [blk]) == ""

-- The real `hoistStmt` keeps `blk` (`hoistStmtWith`'s last arm): the
-- elaborator itself does not take the cycle; only the unguarded shape does.
#guard match (hoistStmtWith C0 (elabRec C0 ()) blk).runFrom' sc0 ([], 0) with
  | .ok (P, s) => P.isEmpty && reprStr s == reprStr blk
  | .error _ => false

/-- **The `elabStmtsP` arm's stability forces its head decrease**, with no
guard: over a record whose `elabStmtP` and `elabStmtsP` succeed, the arm
succeeds, and over its cut it fails unless `elabStmtP s` is below. -/
theorem stmtsStep_head_lt {α : Type} [WellFoundedRelation α] {C : Contract}
    (μ : ElabMeasure α) (h : Stable μ (ElabPreds.top C) μ.elabStmtsP (elabStmtsStep C))
    (s : RawStmt) (ss : List RawStmt) (sc : ElabScope) :
    WellFoundedRelation.rel (μ.elabStmtP s sc) (μ.elabStmtsP (s :: ss) sc) := by
  refine Classical.byContradiction fun hn => ?_
  let r : ElabRec C := { (default : ElabRec C) with
    elabStmtP := fun _ => pure [], elabStmtsP := fun _ => pure [] }
  have hb : MeetsBelow μ (ElabPreds.top C) (μ.elabStmtsP (s :: ss) sc) r :=
    ⟨fun _ _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ _ _ => trivial,
     fun _ _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ _ _ => trivial,
     fun _ _ _ _ _ _ _ _ _ => trivial⟩
  have he := congrArg (fun x => (x.run ([], 0)).run {}) (h r (s :: ss) sc hb)
  have hc : ((cut μ (μ.elabStmtsP (s :: ss) sc) r).elabStmtP s).run sc =
      (throw "" : ElabM (SProg C)).run sc :=
    (cutF_run ..).trans (if_neg hn)
  simp only [elabStmtsStep, ReaderT.run, bind, ReaderT.bind] at he hc
  rw [hc] at he
  cases he

/-- **The cycle**: the three decreases unguarded `Stable` would need along
`elabStmtP blk → elabStmt1 forT → elabStmtsP [blk] → elabStmtP blk` cannot all
hold.  The third is `stmtsStep_head_lt`; the first two are what the `#guard`s
(1) and (2) show the arms depend on, unproved here: a proof would evaluate
`elabStmtPWith` and `elabStmt1With` in the kernel. -/
theorem rel_cycle_forT_blk {α : Type} [WellFoundedRelation α] (μ : ElabMeasure α)
    (h1 : WellFoundedRelation.rel (μ.elabStmt1 forT sc0) (μ.elabStmtP blk sc0))
    (h2 : WellFoundedRelation.rel (μ.elabStmtsP [blk] sc0) (μ.elabStmt1 forT sc0))
    (hst : Stable μ (ElabPreds.top C0) μ.elabStmtsP (elabStmtsStep C0)) : False :=
  rel_cycle3 h1 (stmtsStep_head_lt μ hst blk [] sc0) h2

end Counterexample

end Solidity.Examples.ElabTotalMeasure
