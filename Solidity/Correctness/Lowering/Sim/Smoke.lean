import Solidity.Correctness.Lowering.Sim.Match.Cases
import Solidity.Source.HorizonFuel

/-!
# The case interface on two arms of `elabStmt1With`

What of `Sim/Match/Cases.lean` is proved here, at an arbitrary callback record:

* `source_stable`: the stability clause of `RunSim`, for every body (Source
  horizon monotonicity, `Source.belowAt`); `runSim_of` then reduces `RunSim`
  to `LowerFresh` and the forward and backward clauses (total initial
  matching is `initial_matching`).
* `jump_arm`: the leaf conjunct of `StmtCases` for `elabStmt1With` on
  `return`, `break`, `continue` and `_`. The arm refuses them, so it has no
  successful output: the flag-based lowering has to remove every jump before
  elaboration. Its forward, stability and backward clauses hold of no run.
* `revert_arm_of`: the leaf conjunct for `elabStmt1With` on `revert();`, from
  the Source side of the bodies it is the lowering of (`SourceReverts` and
  `LowerFresh`). The elaboration and target side is proved: the arm's output
  is one `Stmt.revert` (`revert_ran`), every placement of it by `SProg.chain`
  keeps the context and halts with `revert` at every fuel (`revert_placed`),
  which `HaltMatch` matches with a Source revert without data.

Not proved: the premise of `revert_arm_of`. It is not a fact about the arm:
it needs the standalone lowering inverted at a body whose output is
`[.revert]` (`lowerLoops none` on every spelled statement, loops included)
and the Source typing of `revert()` inverted in the canonical unit
(`Total.Decode.unit`).
-/

namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals (ElabRan)
open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)
open Solidity.Correctness.Lowering.Checker (Output)

variable [FreshNames]

omit [FreshNames] in
/-- **Stability**, for every body: a Source run that completes at a horizon is
the run at every larger horizon. -/
theorem source_stable (b : Body) (G : Source.Glob b.E) (F : Source.Fr) (nps : Nat)
    (ph : Option (Source.Ph b.E)) (src : Source.EMState b.E b.ctx) {n n' : Nat} (le : n ≤ n')
    (done : (sourceRun b G F n nps ph src).1 ≠ .error .timeout) :
    sourceRun b G F n' nps ph src = sourceRun b G F n nps ph src :=
  (Source.Below.mono (f := fun k => Source.execS G F k nps ph b.input.resolved src.1)
    (fun k => (Source.belowAt G k).execS F nps ph b.input.resolved src.1) le).eq_of_done _ done

variable (C : Contract)

/-- The `revert();` arm emits one `Stmt.revert` in the locals in scope and keeps the state. -/
theorem revert_ran (rc : ElabRec C) {sc : ElabScope} {st st' : ECtx × Nat} {P : SProg C}
    (ran : ElabRan (elabStmt1With C rc .revert) sc st P st') :
    P = [.of (ECtx.toNCtx st.1) .revert] ∧ st' = st := by
  obtain ⟨m, m', run⟩ := ran
  have h : elabStmt1With C rc .revert = (do pure [.of (← nctx) .revert]) := rfl
  rw [h] at run
  cases run
  exact ⟨rfl, rfl⟩

/-- A placed `Stmt.revert` keeps the context and halts with `revert`. -/
theorem revert_place {ns : List Var} {Γ : Ctx} {Γn : NCtx}
    {r : (Δ' : Ctx) × Stmt C Γ Δ'}
    (placed : (SStmt.of Γn (Stmt.revert (C := C))).place ns Γ = .ok r) :
    Nonempty (Thin Γ r.1) ∧ ∀ (n : Nat) (σ : State C Γ), r.2.runF n σ = .error .revert := by
  unfold SStmt.place at placed
  split at placed
  · rename_i h
    obtain ⟨h₁, h₂⟩ := h
    cases placed
    subst h₁
    exact ⟨⟨.refl⟩, fun _ _ => rfl⟩
  · split at placed
    · cases placed
      exact ⟨⟨.refl⟩, fun _ _ => rfl⟩
    · cases placed

/-- The block of one `Stmt.revert` keeps the context and halts with `revert` at
every fuel. -/
theorem revert_placed {ns : List Var} {Γ : Ctx} {Γn : NCtx} {B : Blk C Γ}
    (placed : SProg.chain ns Γ [SStmt.of Γn (Stmt.revert (C := C))] = .ok B) :
    Nonempty (Thin Γ B.1) ∧ ∀ (n : Nat) (σ : State C Γ), B.2.runF n σ = .error .revert := by
  unfold SProg.chain at placed
  cases hp : (SStmt.of Γn (Stmt.revert (C := C))).place ns Γ with
  | error e => rw [hp] at placed; cases placed
  | ok r =>
    obtain ⟨Δ₁, s⟩ := r
    rw [hp] at placed
    cases placed
    obtain ⟨emb, hs⟩ := revert_place C hp
    refine ⟨emb, fun n σ => ?_⟩
    show TRun.seq (s.runF n) _ σ = _
    simp only [TRun.seq, hs n σ]

omit [FreshNames] in
/-- **`RunSim` from its lowering and run clauses**: total initial matching and
stability hold of every associated body. -/
theorem runSim_of {b : Body} {u : Emitted} {m : ContextMap b.ctx u.Γ} (assoc : diagram.Assoc b u m)
    (fresh : LowerFresh b u) (emb : Thin u.Γ u.output.program.1)
    (runs : ∀ (G : Source.Glob b.E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph b.E))
      (src : Source.EMState b.E b.ctx) (tgt : State u.C u.Γ),
      m.Related (fun τ v => diagram.valRel τ v) src.1 tgt.env → diagram.globRel src.2 tgt →
      (∀ n, (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
        diagram.Final m emb (sourceRun b G F n nps ph src)
          (u.output.program.2.runF (diagram.fuel n) tgt)) ∧
      (∀ n, u.output.program.2.runF n tgt ≠ .error .diverge →
        ∃ j, diagram.Final m emb (sourceRun b G F j nps ph src)
          (u.output.program.2.runF n tgt))) : RunSim b u m :=
  ⟨fresh, initial_matching b u m assoc, emb, fun G F nps ph src tgt related glob =>
    ⟨(runs G F nps ph src tgt related glob).1,
      fun _ _ le done => source_stable b G F nps ph src le done,
      (runs G F nps ph src tgt related glob).2⟩⟩

/-- **The jump arm** of `elabStmt1With` has no successful output. -/
theorem jump_arm (rc : ElabRec C) : ArmSat C (elabStmt1With C rc) .jump := by
  intro s family sc st P st' ran
  obtain ⟨m, m', run⟩ := ran
  unfold stmtFamily at family
  split at family <;> first | (cases family; done) | cases run

/-- The body's Source run reverts without data at every horizon that completes,
and some horizon completes. -/
def SourceReverts (b : Body) : Prop :=
  ∀ (G : Source.Glob b.E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph b.E))
    (src : Source.EMState b.E b.ctx),
    (∀ n, (sourceRun b G F n nps ph src).1 = .error .timeout ∨
      (sourceRun b G F n nps ph src).1 = .error (.revert [])) ∧
    ∃ j, (sourceRun b G F j nps ph src).1 = .error (.revert [])

/-- **The `revert();` arm** of `elabStmt1With`, forward and backward, from the
Source side of the bodies whose lowering is `[.revert]`. -/
theorem revert_arm_of (rc : ElabRec C)
    (bodies : ∀ (b : Body) (Γ : Ctx) (o : Output C Γ) (m : ContextMap b.ctx Γ),
      o.raw = [.revert] → Lowered b ⟨C, Γ, o⟩ → Threaded b ⟨C, Γ, o⟩ →
      diagram.Assoc b ⟨C, Γ, o⟩ m → LowerFresh b ⟨C, Γ, o⟩ ∧ SourceReverts b) :
    ArmSat C (elabStmt1With C rc) .revert := by
  intro s family sc st P st' ran
  have hs : s = .revert := by
    unfold stmtFamily at family
    split at family <;> first | (cases family; done) | rfl
  subst hs
  obtain ⟨rfl, rfl⟩ := revert_ran C rc ran
  intro b Γ o m run lowered threaded _ assoc
  obtain ⟨raw, _, _, parts, _, _, placed⟩ := run
  rw [parts] at placed
  obtain ⟨fresh, source⟩ := bodies b Γ o m raw lowered threaded assoc
  obtain ⟨⟨emb⟩, target⟩ := revert_placed C placed
  refine runSim_of assoc fresh emb fun G F nps ph src tgt _ _ => ?_
  obtain ⟨each, j, some⟩ := source G F nps ph src
  have final (k n : Nat) (h : (sourceRun b G F k nps ph src).1 = .error (.revert [])) :
      diagram.Final m emb (sourceRun b G F k nps ph src)
        (Prog.runF n (Emitted.mk C Γ o).output.program.2 tgt) := by
    unfold Diagram.Final
    rw [h, target n tgt]
    exact .inl rfl
  exact ⟨fun n done => final n _ ((each n).resolve_left done), fun n _ => ⟨j, final j n some⟩⟩

end Solidity.Correctness.Lowering.Sim
