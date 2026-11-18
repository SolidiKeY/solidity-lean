import Solidity.Syntax.Elab.Measure
import Solidity.Syntax.Elab.Arms

/-!
# The output guard of the elaborator knot: no guard over the five fields

`Syntax/Elab/Measure.lean` asks which guard `J : ElabPreds C`, a predicate on
the runs of `hoist`, `hoistStmt`, `elabStmtP`, `elabStmt1` and `elabStmtsP`,
makes the five arms `Stable`.  None that the arms keep does: a guard is kept
over every record whose five fields meet it, and `hoistStmtWith` returns what
the record's other fields return.

* `hoistStmtWith_assign_num`: at `l = n;`, `hoistStmtWith C r` is
  `r.hoistAssign l n`, a field that is not one of the five.
* `ElabPreds.free_at_assign`: so a guard that `hoistStmtWith` keeps
  (`ElabPreds.HoistStmtKept`) holds of every output and end state at
  `l = n;`: it bounds nothing there.
* `stmtsArm_head_lt`: under any guard, `elabStmtsP`'s arm is stable only if
  its head is below it (`rel_cycle4` closes the cycle of
  `Solidity/Examples/ElabTotal/Guard.lean`).

What a guard can be stated over is the knot's own record: `OffFive rc r` (`r`
is `rc` off the five fields, as every `ElabMeasure.cut` of `rc` is) and
`ElabMeasure.StableAt` (the arm's decrease at `rc`).  Clause 2 of
`Solidity.Goals.elabKernelTotal` follows from these
(`Solidity/Examples/ElabTotal/Guard.lean`).
-/

namespace Solidity

open Semantics

/-- No element of a well-founded relation lies on a cycle of four. -/
theorem rel_cycle4 {α : Type} [WellFoundedRelation α] {a b c d : α}
    (h1 : WellFoundedRelation.rel a b) (h2 : WellFoundedRelation.rel b c)
    (h3 : WellFoundedRelation.rel c d) (h4 : WellFoundedRelation.rel d a) : False :=
  WellFounded.induction (C := fun a => ∀ b c d, WellFoundedRelation.rel a b →
      WellFoundedRelation.rel b c → WellFoundedRelation.rel c d →
      WellFoundedRelation.rel d a → False)
    WellFoundedRelation.wf a (fun _ ih b c d h1 h2 h3 h4 => ih d h4 _ b c h4 h1 h2 h3)
    b c d h1 h2 h3 h4

/-- A field that fails meets every predicate. -/
theorem runsMeet_throw {β γ : Type} {Q : β → ElabScope → ECtx × Nat → γ → ECtx × Nat → Prop}
    {e : String} {x : β} {sc : ElabScope} : RunsMeet Q (fun _ => (throw e : ElabM γ)) x sc := by
  intro st b st' m m' hr
  cases hr

variable [FreshNames] {C : Contract}

/-- **`hoistStmt`'s arm at `l = n;` is the record's `hoistAssign`**, at every
record, target, literal and scope. -/
theorem hoistStmtWith_assign_num (r : ElabRec C) (l : RawExpr) (n : Nat) (sc : ElabScope) :
    (hoistStmtWith C r (.assign l (.num n))).run sc = (r.hoistAssign l (.num n)).run sc := by
  funext st m
  simp only [hoistStmtWith]
  rfl

/-- The five fields of `r` meet `J`, at every run. -/
def ElabPreds.Meets (J : ElabPreds C) (r : ElabRec C) : Prop :=
  (∀ x sc, RunsMeet J.hoist r.hoist x sc) ∧ (∀ x sc, RunsMeet J.hoistStmt r.hoistStmt x sc) ∧
  (∀ x sc, RunsMeet J.elabStmtP r.elabStmtP x sc) ∧ (∀ x sc, RunsMeet J.elabStmt1 r.elabStmt1 x sc) ∧
  (∀ x sc, RunsMeet J.elabStmtsP r.elabStmtsP x sc)

/-- `hoistStmt`'s arm keeps the guard: over every record whose five fields
meet `J`, its runs meet `J.hoistStmt`. -/
def ElabPreds.HoistStmtKept (J : ElabPreds C) : Prop :=
  ∀ r : ElabRec C, J.Meets r → ∀ x sc, RunsMeet J.hoistStmt (hoistStmtWith C r) x sc

/-- A record whose five fields fail and whose `hoistAssign` returns `b`,
ending in `st'`. -/
def assignRec (C : Contract) (b : SProg C × RawStmt) (st' : ECtx × Nat) : ElabRec C :=
  { (default : ElabRec C) with
    hoist := fun _ => throw "", hoistStmt := fun _ => throw "", elabStmtP := fun _ => throw "",
    elabStmt1 := fun _ => throw "", elabStmtsP := fun _ => throw "",
    hoistAssign := fun _ _ _ _ m => .ok ((b, st'), m) }

/-- **A kept guard bounds nothing at `l = n;`**: it holds of every output and
end state there. -/
theorem ElabPreds.free_at_assign {J : ElabPreds C} (hJ : J.HoistStmtKept) (l : RawExpr) (n : Nat)
    (sc : ElabScope) (st : ECtx × Nat) (b : SProg C × RawStmt) (st' : ECtx × Nat) :
    J.hoistStmt (.assign l (.num n)) sc st b st' := by
  have hm : J.Meets (assignRec C b st') :=
    ⟨fun _ _ => runsMeet_throw, fun _ _ => runsMeet_throw, fun _ _ => runsMeet_throw,
     fun _ _ => runsMeet_throw, fun _ _ => runsMeet_throw⟩
  refine hJ _ hm (.assign l (.num n)) sc st b st' {} {} ?_
  rw [hoistStmtWith_assign_num]
  rfl

namespace ElabMeasure

variable {α : Type} [WellFoundedRelation α]

omit [FreshNames] in
/-- **`elabStmtsP`'s arm is stable only if its head is below it**, under any
guard: over a record whose `elabStmtP` fails with `"head"` the arm fails so,
and over its cut it fails with `""` unless `elabStmtP s` is below. -/
theorem stmtsArm_head_lt (μ : ElabMeasure α) (J : ElabPreds C)
    (h : Stable μ J μ.elabStmtsP (stmtsArm (C := C))) (s : RawStmt) (ss : List RawStmt)
    (sc : ElabScope) :
    WellFoundedRelation.rel (μ.elabStmtP s sc) (μ.elabStmtsP (s :: ss) sc) := by
  refine Classical.byContradiction fun hn => ?_
  let r : ElabRec C := { (default : ElabRec C) with
    hoist := fun _ => throw "", hoistStmt := fun _ => throw "", elabStmtP := fun _ => throw "head",
    elabStmt1 := fun _ => throw "", elabStmtsP := fun _ => throw "" }
  have hb : MeetsBelow μ J (μ.elabStmtsP (s :: ss) sc) r :=
    ⟨fun _ _ _ => runsMeet_throw, fun _ _ _ => runsMeet_throw, fun _ _ _ => runsMeet_throw,
     fun _ _ _ => runsMeet_throw, fun _ _ _ => runsMeet_throw⟩
  have he := congrArg (fun x => (x.run ([], 0)).run {}) (h r (s :: ss) sc hb)
  have hc : ((cut μ (μ.elabStmtsP (s :: ss) sc) r).elabStmtP s).run sc =
      (throw "" : ElabM (SProg C)).run sc :=
    (cutF_run ..).trans (if_neg hn)
  simp only [stmtsArm, ReaderT.run, bind, ReaderT.bind] at he hc
  rw [hc] at he
  exact absurd (Except.error.inj he) (by decide)

/-- `r` is `rc` off the five recursive fields. -/
def OffFive (rc r : ElabRec C) : Prop :=
  r = { rc with hoist := r.hoist, hoistStmt := r.hoistStmt, elabStmtP := r.elabStmtP,
                elabStmt1 := r.elabStmt1, elabStmtsP := r.elabStmtsP }

omit [FreshNames] in
theorem offFive_cut (μ : ElabMeasure α) (a : α) (rc : ElabRec C) : OffFive rc (cut μ a rc) := rfl

/-- **The arm's decrease at `rc`**: `Stable`, at the one record `rc`, whose
other fields the guard may then describe. -/
def StableAt {β γ : Type} (μ : ElabMeasure α) (J : ElabPreds C) (m : β → ElabScope → α)
    (arm : ElabRec C → β → ElabM γ) (rc : ElabRec C) : Prop :=
  ∀ x sc, MeetsBelow μ J (m x sc) rc → (arm (cut μ (m x sc) rc) x).run sc = (arm rc x).run sc

omit [FreshNames] in
theorem Stable.stableAt {β γ : Type} {μ : ElabMeasure α} {J : ElabPreds C} {m : β → ElabScope → α}
    {arm : ElabRec C → β → ElabM γ} (h : Stable μ J m arm) (rc : ElabRec C) :
    StableAt μ J m arm rc :=
  fun x sc hb => h rc x sc hb

end ElabMeasure

end Solidity
