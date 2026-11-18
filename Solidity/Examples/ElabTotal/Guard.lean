import Solidity.Examples.ElabTotal.Measure
import Solidity.Syntax.Elab.Guard

/-!
# Checks: no output guard over the five fields

**No guard: `hoistStmtWith` at `x = 0;`.**  A guard `J : ElabPreds C` that the
arms keep (`GuardKept`, the hypothesis of `elabKernelInduction_of_stable`)
holds of every output of `hoistStmt` at `l = n;` (`guardKept_free_at_assign`):
there `hoistStmtWith C r` is `r.hoistAssign l n`, and `GuardKept` ranges over
every record, whose `hoistAssign` is not one of the five guarded fields.  So
no kept guard bounds what `hoistStmt` returns, and the nested call
`elabStmt1 (← hoistStmt s)` of `elabStmtPWith` is unbounded under any of them.

With `hoistStmt (x = 0;)` returning `revert E(x = 0);`, the arms call, all at
the scope `sc0`:

    elabStmtP (x = 0;)            -- elabStmtPWith, its hoistStmt returning sS
      → elabStmt1 (revert E(x = 0);)  -- elabStmt1With: eagerArgsWith rc.hoist
      → hoist (x = 0)             -- hoistWith, an assignment's value
      → elabStmtsP [x = 0;]       -- elabStmtsStep, at its head
      → elabStmtP (x = 0;)

Each arrow is a call the arm makes through its record whose failure is the
arm's (the `#guard`s: a spy's error, and `""` where the field fails
silently, as a cut field does), and every record used meets every kept guard
below (`guardKept_free_at_assign`; `hoistWith_num` for `hoist 0`, which is
`([], 0)` over every record).  So `ArmsStable μ J` needs the four decreases of
`no_guard_cycle`, a cycle.  The last is proved from `Stable`
(`stmtsStep_head_lt_guarded`); the first three are shown by evaluation only,
as in `Examples/ElabTotal/Measure.lean`: `elabStmtPWith` runs
`RawExpr.mapM`, which is `partial`, so the kernel cannot evaluate it.

**The shape that remains** (`elabKernelInduction_of_stableAt`): clause 2
follows from the arms' decrease at the knot's record `rc` alone
(`ElabMeasure.StableAt`) and a guard kept over the records that are `rc` off
the five fields (`GuardKeptAt`), which is all the proof of
`elabKernelInduction_of_stable` uses.  There the guard's proof may use what
`rc.hoistAssign`, `rc.hoistTop`, `rc.hoistArgs` and `rc.hoistCallArgs`
return.
-/

namespace Solidity.Examples.ElabTotalGuard

open Solidity Semantics Goals ElabMeasure Solidity.Examples.ElabTotalMeasure

section Free

variable [FreshNames] {C : Contract}

/-- A guard the arms keep is kept by `hoistStmt`'s arm. -/
theorem GuardKept.hoistStmtKept {J : ElabPreds C} (hJ : GuardKept J) : J.HoistStmtKept := by
  intro r ⟨hH, hS, hP, h1, hL⟩
  exact elabSat_iff.1 (hJ r (elabSat_iff.2 hH) (elabSat_iff.2 hS) (elabSat_iff.2 hP)
    (elabSat_iff.2 h1) (elabSat_iff.2 hL)).2.1

/-- **No guard**: a guard the arms keep holds of every output and end state
of `hoistStmt` at `l = n;`. -/
theorem guardKept_free_at_assign {J : ElabPreds C} (hJ : GuardKept J) (l : RawExpr) (n : Nat)
    (sc : ElabScope) (st : ECtx × Nat) (b : SProg C × RawStmt) (st' : ECtx × Nat) :
    J.hoistStmt (.assign l (.num n)) sc st b st' :=
  ElabPreds.free_at_assign (GuardKept.hoistStmtKept hJ) l n sc st b st'

/-- `hoist`'s arm at `0`: the literal, nothing captured, over every record. -/
theorem hoistWith_num (r : ElabRec C) : hoistWith C r (.num 0) = pure ([], .num 0) := rfl

omit [FreshNames] in
/-- **`elabStmtsP`'s arm is stable only if its head is below it**, under any
guard. -/
theorem stmtsStep_head_lt_guarded {α : Type} [WellFoundedRelation α] (μ : ElabMeasure α)
    (J : ElabPreds C) (h : Stable μ J μ.elabStmtsP (elabStmtsStep C)) (s : RawStmt)
    (ss : List RawStmt) (sc : ElabScope) :
    WellFoundedRelation.rel (μ.elabStmtP s sc) (μ.elabStmtsP (s :: ss) sc) :=
  stmtsArm_head_lt μ J ((funext elabStmtsStep_eq : elabStmtsStep C = stmtsArm) ▸ h) s ss sc

end Free

section Counterexample

/-- `x = 0;` -/
def aS : RawStmt := .assign (.name "x") (.num 0)

/-- `x = 0`, the expression. -/
def aE : RawExpr := .assign (.name "x") (.num 0)

/-- `revert E(x = 0);` -/
def sS : RawStmt := .revertErr "E" [aE]

/-- A record whose five fields fail silently. -/
def silent : ElabRec C0 :=
  { (default : ElabRec C0) with
    hoist := fun _ => throw "", hoistStmt := fun _ => throw "", elabStmtP := fun _ => throw "",
    elabStmt1 := fun _ => throw "", elabStmtsP := fun _ => throw "" }

-- (0) `hoistStmtWith` at `x = 0;` returns what the record's `hoistAssign`
-- does: here `revert E(x = 0);`, and et3a's `for` loop `forT`.
#guard match (hoistStmtWith C0 (assignRec C0 ([], sS) ([], 0)) aS).runFrom' sc0 ([], 0) with
  | .ok (P, s) => P.isEmpty && reprStr s == reprStr sS
  | .error _ => false

#guard match (hoistStmtWith C0 (assignRec C0 ([], forT) ([], 0)) aS).runFrom' sc0 ([], 0) with
  | .ok (P, s) => P.isEmpty && reprStr s == reprStr forT
  | .error _ => false

-- (1) `elabStmtPWith` at `x = 0;` calls `hoistStmt` at `x = 0;`, then
-- `elabStmt1` at what it returns, at `sc0`.
#guard errOf (elabStmtPWith C0 { silent with hoistStmt := spy "hoistStmt" } aS) ==
  s!"hoistStmt {reprStr aS} @ {scopeTag sc0}"

/-- The record whose `hoistStmt` returns `revert E(x = 0);`. -/
def recS : ElabRec C0 := { silent with hoistStmt := fun _ => pure ([], sS) }

#guard errOf (elabStmtPWith C0 { recS with elabStmt1 := spy "elabStmt1" } aS) ==
  s!"elabStmt1 {reprStr sS} @ {scopeTag sc0}"

#guard errOf (elabStmtPWith C0 silent aS) == ""

#guard errOf (elabStmtPWith C0 recS aS) == ""

-- (2) `elabStmt1With` at `revert E(x = 0);` calls `hoist` at `x = 0`, at `sc0`.
#guard errOf (elabStmt1With C0 { silent with hoist := spy "hoist" } sS) ==
  s!"hoist {reprStr aE} @ {scopeTag sc0}"

#guard errOf (elabStmt1With C0 silent sS) == ""

-- (3) `hoistWith` at `x = 0` calls `hoist` at `0` (`hoistWith_num`: `([], 0)`
-- over every record), then `elabStmtsP` at `[x = 0;]`, at `sc0`.
#guard errOf (hoistWith C0 { silent with hoist := spy "hoist" } aE) ==
  s!"hoist {reprStr (RawExpr.num 0)} @ {scopeTag sc0}"

/-- The record whose `hoist` returns its input, nothing captured. -/
def recH : ElabRec C0 := { silent with hoist := fun e => pure ([], e) }

#guard errOf (hoistWith C0 { recH with elabStmtsP := spy "elabStmtsP" } aE) ==
  s!"elabStmtsP {reprStr [aS]} @ {scopeTag sc0}"

#guard errOf (hoistWith C0 silent aE) == ""

#guard errOf (hoistWith C0 recH aE) == ""

-- (4) `elabStmtsStep` at `[x = 0;]` calls `elabStmtP` at `x = 0;`: the cycle
-- is closed (`stmtsStep_head_lt_guarded`).
#guard errOf (elabStmtsStep C0 { silent with elabStmtP := spy "elabStmtP" } [aS]) ==
  s!"elabStmtP {reprStr aS} @ {scopeTag sc0}"

/-- **The cycle, under any guard**: the four decreases `ArmsStable μ J` needs
along `elabStmtP (x = 0;) → elabStmt1 (revert E(x = 0);) → hoist (x = 0) →
elabStmtsP [x = 0;] → elabStmtP (x = 0;)` cannot all hold.  The fourth is
`stmtsStep_head_lt_guarded`; the first three are what the `#guard`s (1) to (3)
show the arms depend on, over records every kept guard admits
(`guardKept_free_at_assign`, `hoistWith_num`), unproved here. -/
theorem no_guard_cycle {α : Type} [WellFoundedRelation α] (μ : ElabMeasure α)
    (J : ElabPreds C0)
    (h1 : WellFoundedRelation.rel (μ.elabStmt1 sS sc0) (μ.elabStmtP aS sc0))
    (h2 : WellFoundedRelation.rel (μ.hoist aE sc0) (μ.elabStmt1 sS sc0))
    (h3 : WellFoundedRelation.rel (μ.elabStmtsP [aS] sc0) (μ.hoist aE sc0))
    (hst : Stable μ J μ.elabStmtsP (elabStmtsStep C0)) : False :=
  rel_cycle4 h1 (stmtsStep_head_lt_guarded μ J hst aS [] sc0) h3 h2

end Counterexample

section At

variable [FreshNames] {C : Contract} {α : Type} [WellFoundedRelation α]

/-- The five arms decrease under `μ` at the record `rc`, relative to `J`. -/
def ArmsStableAt (μ : ElabMeasure α) (J : ElabPreds C) (rc : ElabRec C) : Prop :=
  StableAt μ J μ.hoist (hoistWith C) rc ∧ StableAt μ J μ.hoistStmt (hoistStmtWith C) rc ∧
  StableAt μ J μ.elabStmtP (elabStmtPWith C) rc ∧ StableAt μ J μ.elabStmt1 (elabStmt1With C) rc ∧
  StableAt μ J μ.elabStmtsP (elabStmtsStep C) rc

/-- The arms keep the guard over the records that are `rc` off the five
fields. -/
def GuardKeptAt (J : ElabPreds C) (rc : ElabRec C) : Prop :=
  ∀ r : ElabRec C, OffFive rc r → ElabSat J.hoist r.hoist → ElabSat J.hoistStmt r.hoistStmt →
    ElabSat J.elabStmtP r.elabStmtP → ElabSat J.elabStmt1 r.elabStmt1 →
    ElabSat J.elabStmtsP r.elabStmtsP →
    ElabSat J.hoist (hoistWith C r) ∧ ElabSat J.hoistStmt (hoistStmtWith C r) ∧
      ElabSat J.elabStmtP (elabStmtPWith C r) ∧ ElabSat J.elabStmt1 (elabStmt1With C r) ∧
      ElabSat J.elabStmtsP (elabStmtsStep C r)

omit [WellFoundedRelation α] in
/-- A record that is `rc` off the five fields and meets `Q` and `J` there
meets, at its arms, what `hQ` and `hJ` give. -/
theorem arms_meet {rc r : ElabRec C} {J : ElabPreds C} (hr : OffFive rc r)
    {QH : RawExpr → ElabScope → ECtx × Nat → SProg C × RawExpr → ECtx × Nat → Prop}
    {QS : RawStmt → ElabScope → ECtx × Nat → SProg C × RawStmt → ECtx × Nat → Prop}
    {QP Q1 : RawStmt → ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop}
    {QL : List RawStmt → ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop}
    (hQ : ∀ r : ElabRec C, ElabSat QH r.hoist → ElabSat QS r.hoistStmt →
        ElabSat QP r.elabStmtP → ElabSat Q1 r.elabStmt1 → ElabSat QL r.elabStmtsP →
      ElabSat QH (hoistWith C r) ∧ ElabSat QS (hoistStmtWith C r) ∧
        ElabSat QP (elabStmtPWith C r) ∧ ElabSat Q1 (elabStmt1With C r) ∧
        ElabSat QL (elabStmtsStep C r))
    (hJ : GuardKeptAt J rc)
    (cH : ∀ x sc, RunsMeet (fun x sc st b st' => QH x sc st b st' ∧ J.hoist x sc st b st') r.hoist x sc)
    (cS : ∀ x sc, RunsMeet (fun x sc st b st' => QS x sc st b st' ∧ J.hoistStmt x sc st b st')
      r.hoistStmt x sc)
    (cP : ∀ x sc, RunsMeet (fun x sc st b st' => QP x sc st b st' ∧ J.elabStmtP x sc st b st')
      r.elabStmtP x sc)
    (c1 : ∀ x sc, RunsMeet (fun x sc st b st' => Q1 x sc st b st' ∧ J.elabStmt1 x sc st b st')
      r.elabStmt1 x sc)
    (cL : ∀ x sc, RunsMeet (fun x sc st b st' => QL x sc st b st' ∧ J.elabStmtsP x sc st b st')
      r.elabStmtsP x sc) :
    (ElabSat QH (hoistWith C r) ∧ ElabSat QS (hoistStmtWith C r) ∧
        ElabSat QP (elabStmtPWith C r) ∧ ElabSat Q1 (elabStmt1With C r) ∧
        ElabSat QL (elabStmtsStep C r)) ∧
      ElabSat J.hoist (hoistWith C r) ∧ ElabSat J.hoistStmt (hoistStmtWith C r) ∧
        ElabSat J.elabStmtP (elabStmtPWith C r) ∧ ElabSat J.elabStmt1 (elabStmt1With C r) ∧
        ElabSat J.elabStmtsP (elabStmtsStep C r) :=
  ⟨hQ r
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cH x sc st b st' m m' hr).1)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cS x sc st b st' m m' hr).1)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cP x sc st b st' m m' hr).1)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (c1 x sc st b st' m m' hr).1)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cL x sc st b st' m m' hr).1),
    hJ r hr
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cH x sc st b st' m m' hr).2)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cS x sc st b st' m m' hr).2)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cP x sc st b st' m m' hr).2)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (c1 x sc st b st' m m' hr).2)
      (elabSat_iff.2 fun x sc st b st' m m' hr => (cL x sc st b st' m m' hr).2)⟩

/-- **Clause 2 from the arms' guarded decrease at the knot's record**: the
proof of `elabKernelInduction_of_stable`, which applies the arms' decrease at
`rc` and the guard's preservation at the cuts of `rc` only. -/
theorem elabKernelInduction_of_stableAt (μ : ElabMeasure α) (J : ElabPreds C) (rc : ElabRec C)
    (hfix : ElabKernelFix C rc) (hst : ArmsStableAt μ J rc) (hJ : GuardKeptAt J rc) :
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
    obtain ⟨⟨qH, qS, qP, q1, qL⟩, jH, jS, jP, j1, jL⟩ :=
      arms_meet (offFive_cut μ a rc) hQ hJ (cutF_meets bK.1) (cutF_meets bK.2.1)
        (cutF_meets bK.2.2.1) (cutF_meets bK.2.2.2.1) (cutF_meets bK.2.2.2.2)
    exact ⟨field_meets hH (fun x sc hx => by subst hx; exact hst.1 x sc bJ) qH jH,
      field_meets hS (fun x sc hx => by subst hx; exact hst.2.1 x sc bJ) qS jS,
      field_meets hP (fun x sc hx => by subst hx; exact hst.2.2.1 x sc bJ) qP jP,
      field_meets h1 (fun x sc hx => by subst hx; exact hst.2.2.2.1 x sc bJ) q1 j1,
      field_meets hL (fun x sc hx => by subst hx; exact hst.2.2.2.2 x sc bJ) qL jL⟩
  exact ⟨elabSat_iff.2 fun x sc st b st' m m' hr => ((key _).1 x sc rfl st b st' m m' hr).1,
    elabSat_iff.2 fun x sc st b st' m m' hr => ((key _).2.1 x sc rfl st b st' m m' hr).1,
    elabSat_iff.2 fun x sc st b st' m m' hr => ((key _).2.2.1 x sc rfl st b st' m m' hr).1,
    elabSat_iff.2 fun x sc st b st' m m' hr => ((key _).2.2.2.1 x sc rfl st b st' m m' hr).1,
    elabSat_iff.2 fun x sc st b st' m m' hr => ((key _).2.2.2.2 x sc rfl st b st' m m' hr).1⟩

/-- `elabKernelInduction_of_stable` is the instance at guards kept over
every record. -/
theorem guardKeptAt_of_guardKept {J : ElabPreds C} (hJ : GuardKept J) (rc : ElabRec C) :
    GuardKeptAt J rc :=
  fun r _ => hJ r

end At

end Solidity.Examples.ElabTotalGuard
