import Solidity.Theory.Progress.Controls

/-!
Additive audit of frozen progress statements. These witnesses pack all inputs
and premise proofs of the named statement together. Call-free CallsOKX alone
is never counted as a witness for a statement requiring an admitted call.
Source fuel and compiler pipeline are not EVM gas and fork observations.
-/
namespace H62.AuditTheories

open Solidity Solidity.Source Solidity.Source.Progress
open Solidity.Source.SemanticsExamples Solidity.Theory.Progress
open Solidity.Theory.Progress.Controls EM

/-- A simultaneous input/premise witness for the exact tuple_stmt_progress
statement, with a successful, nonempty tuple declaration observation. -/
theorem tuple_stmt_progress_joint_witness :
    ∃ (E : Env) (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
      (R : List STy) (M : Bool) (k : SCtx) (Γ Γ' : RCtx)
      (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
      (x : Locals E.layout [] × St E),
      SFrag (StmtExt.none E) (fun _ => False) s ∧ s.OpsOK ∧ BodyFrame nps R Γ ∧
      ∃ result, ((execS G F n nps ph s l).run x).1 = .ok result := by
  refine ⟨E0, G0 .legacy, F0, 10, 0, none, [], false, .body, [], [.bool, .bool],
    pairDecl, .nil, (.nil, s0), pairDeclAt_frag _, ?_, ⟨[], [], rfl, rfl⟩, _, pairDecl_run⟩
  simp only [pairDeclAt, RStmt.OpsOK, RExpr.OpsOK, RArgs.OpsOK, and_self]

/-- A simultaneous input/premise witness for stmt_progress. Its global
program/extension premises and the actual statement premises share one input. -/
theorem stmt_progress_joint_witness :
    ∃ (E : Env) (X : StmtExt E) (A : Decl → Prop) (G : Glob E) (c : String)
      (F : Fr) (n nps : Nat) (ph : Option (Ph E)) (R : List STy) (M : Bool)
      (k : SCtx) (Γ Γ' : RCtx) (s : RStmt E R M k Γ Γ')
      (l : Locals E.layout Γ) (x : Locals E.layout [] × St E),
      CallsOKX X A G c ∧ X.Sound G A (· = c) ∧ F.contract = c ∧
      SFrag X A s ∧ s.OpsOK ∧ BodyFrame nps R Γ ∧
      ∃ result, ((execS G F n nps ph s l).run x).1 = .ok result := by
  obtain ⟨E, G, F, n, nps, ph, R, M, k, Γ, Γ', s, l, x, hf, ho, hfr, hs⟩ :=
    tuple_stmt_progress_joint_witness
  exact ⟨E, StmtExt.none E, (fun _ => False), G, F.contract, F, n, nps, ph,
    R, M, k, Γ, Γ', s, l, x, callsOKX_none _ G _, StmtExt.none_sound G _ _,
    rfl, hf, ho, hfr, hs⟩

/-- The same supported declaration returns its two booleans under both source
compiler pipelines, at this interpreter horizon. This is source success only. -/
theorem tuple_returns_both_pipelines (p : Roadmap.Pipeline) :
    ((execS (G0 p) F0 10 0 none pairDecl .nil).run (.nil, s0)).1 =
      .ok (.normal (.cons (.bool true) (.cons (.bool true) .nil))) := by
  cases p <;> rfl

/-- The successful tuple observation rejects any always-error source runner,
including a runner which always reverts or always times out. -/
theorem tuple_excludes_always_error (p : Roadmap.Pipeline) (halt : Halt) :
    ((execS (G0 p) F0 10 0 none pairDecl .nil).run (.nil, s0)).1 ≠ .error halt := by
  rw [tuple_returns_both_pipelines p]
  intro h
  cases h

/-- A concrete low-fuel boundary is separate from the successful horizon. -/
theorem tuple_fuel_boundary :
    ((execS (G0 .legacy) F0 5 0 none pairDecl .nil).run (.nil, s0)).1 = .error .timeout ∧
    ((execS (G0 .legacy) F0 10 0 none pairDecl .nil).run (.nil, s0)).1 =
      .ok (.normal (.cons (.bool true) (.cons (.bool true) .nil))) :=
  ⟨pairDecl_timeout, pairDecl_run⟩

/-- Ends admits a timeout without a return: a classification theorem alone
cannot establish the source-success obligation used above. -/
theorem timeout_ends_without_return :
    Ends (.error .timeout : Except Halt Unit) ∧
      ¬ ∃ a : Unit, (.error .timeout : Except Halt Unit) = .ok a := by
  refine ⟨.outOfFuel, ?_⟩
  rintro ⟨a, h⟩
  cases h

/-- The first impossible-input control cannot have a simultaneous witness. -/
theorem no_plain_tuple_input :
    ¬ ∃ (D : Layout) (σs : List STy), Nonempty (Val D (.tuple σs)) := by
  rintro ⟨D, σs, ⟨v⟩⟩
  exact Val.not_tuple v

/-- The second impossible-input control cannot have a simultaneous witness. -/
theorem no_tuple_locals_input :
    ¬ ∃ (D : Layout) (σs : List STy) (Γ : RCtx), Nonempty (Locals D (.tuple σs :: Γ)) := by
  rintro ⟨D, σs, Γ, ⟨l⟩⟩
  exact no_tuple_local l

#print axioms tuple_stmt_progress_joint_witness
#print axioms stmt_progress_joint_witness
#print axioms tuple_returns_both_pipelines
#print axioms tuple_excludes_always_error
#print axioms tuple_fuel_boundary
#print axioms timeout_ends_without_return
#print axioms no_plain_tuple_input
#print axioms no_tuple_locals_input

end H62.AuditTheories
