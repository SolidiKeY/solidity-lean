import Solidity.Backend.FailurePaths.GuardBlockSelection
import Solidity.Backend.FailurePaths.GuardBodySelectionControls

/-! Inhabited root-block statement selection and actual Source scope close in
both pipelines. The chosen code is from public Memory.compileStmt; body, target
machine and refusal boundaries use the existing mixed-context guard fixtures. -/
namespace Solidity.Backend.FailurePaths.GuardBlockSelection.Controls
open Evm Evm.Memory CheckedGuards.Controls
open PrimitivePackets.Comparisons

def statement : Source.RStmt E [] false .body SrcCtx SrcCtx :=
  .block GuardBodySelection.Controls.body
def admitted : View statement :=
  ⟨rfl,SrcCtx,GuardBodySelection.Controls.body,GuardBodySelection.Controls.admitted,rfl⟩

theorem viewed : view statement = some admitted := rfl

theorem lowered : lower (C:=C) maps statement = some (.block GuardSequences.Controls.target) := rfl

theorem public_selected : compile (C:=C) maps 0 fragment statement = some GuardSequences.Controls.code := by
  rw [compile_of_view maps 0 fragment statement admitted viewed]
  exact GuardSequences.Controls.public_selected

theorem public_compilation :
    ∃ (witness : View statement) (program : Prog C TgtCtx TgtCtx)
      (checked : CompiledProg 0 fragment program),
      view statement = some witness ∧
      GuardSequences.lower maps witness.admitted.statements = some program ∧
      Memory.compileProg 0 fragment program = some checked ∧
      Memory.compileStmt 0 fragment (.block program) = some (blockChecked checked) ∧
      (blockChecked checked).code = GuardSequences.Controls.code :=
  selected_public maps 0 fragment statement GuardSequences.Controls.code public_selected

theorem client (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    ∃ value : Bool,
      (Source.execS (globals p) frame 11 0 none statement (locals left right x y hx hy)).run
        (Source.L0 E,original) =
        (if value then (.ok (.normal (locals left right x y hx hy)),(Source.L0 E,original))
         else (.error (.revert []),(Source.L0 E,original))) ∧
      run GuardSequences.Controls.code (machine left right x y hx hy) =
        (if value then .ok (machine left right x y hx hy) 0 else .revert) := by
  obtain ⟨witness,value,chosen,source,target⟩ := selected_correct maps 0 fragment statement
    GuardSequences.Controls.code public_selected (globals p) frame 0
    (locals left right x y hx hy) original (state left right x y hx hy)
    (related left right x y hx hy) (represented left right x y hx hy)
  rw [viewed] at chosen
  cases Option.some.inj chosen
  exact ⟨value,source,target⟩

theorem source_run (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    (Source.execS (globals p) frame 11 0 none statement (locals left right x y hx hy)).run
      (Source.L0 E,original) =
      if left && (left && right) && decide (x < y)
      then (.ok (.normal (locals left right x y hx hy)),(Source.L0 E,original))
      else (.error (.revert []),(Source.L0 E,original)) := by
  obtain ⟨value,source,target⟩ := client p left right x y hx hy
  rw [GuardSequences.Controls.target_run] at target
  cases value <;> cases actual : (left && (left && right) && decide (x < y)) <;>
    simp only [actual,Bool.false_eq_true,if_false,if_true,reduceCtorEq] at target source ⊢
  all_goals exact source

theorem target_run (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    run GuardSequences.Controls.code (machine left right x y hx hy) =
      if left && (left && right) && decide (x < y)
      then .ok (machine left right x y hx hy) 0 else .revert :=
  GuardSequences.Controls.target_run left right x y hx hy

theorem success (p : Roadmap.Pipeline) :
    (Source.execS (globals p) frame 11 0 none statement (locals true true 1 2 (by decide) (by decide))).run
      (Source.L0 E,original) = (.ok (.normal (locals true true 1 2 (by decide) (by decide))),(Source.L0 E,original)) ∧
    run GuardSequences.Controls.code (machine true true 1 2 (by decide) (by decide)) = .ok (machine true true 1 2 (by decide) (by decide)) 0 :=
  ⟨source_run p true true 1 2 (by decide) (by decide),
    target_run true true 1 2 (by decide) (by decide)⟩

theorem first_failure (p : Roadmap.Pipeline) :
    (Source.execS (globals p) frame 11 0 none statement (locals false true 1 2 (by decide) (by decide))).run
      (Source.L0 E,original) = (.error (.revert []),(Source.L0 E,original)) ∧
    run GuardSequences.Controls.code (machine false true 1 2 (by decide) (by decide)) = .revert :=
  ⟨source_run p false true 1 2 (by decide) (by decide),
    target_run false true 1 2 (by decide) (by decide)⟩

theorem middle_failure (p : Roadmap.Pipeline) :
    (Source.execS (globals p) frame 11 0 none statement (locals true false 1 2 (by decide) (by decide))).run
      (Source.L0 E,original) = (.error (.revert []),(Source.L0 E,original)) ∧
    run GuardSequences.Controls.code (machine true false 1 2 (by decide) (by decide)) = .revert :=
  ⟨source_run p true false 1 2 (by decide) (by decide),
    target_run true false 1 2 (by decide) (by decide)⟩

theorem last_failure (p : Roadmap.Pipeline) :
    (Source.execS (globals p) frame 11 0 none statement (locals true true 2 1 (by decide) (by decide))).run
      (Source.L0 E,original) = (.error (.revert []),(Source.L0 E,original)) ∧
    run GuardSequences.Controls.code (machine true true 2 1 (by decide) (by decide)) = .revert :=
  ⟨source_run p true true 2 1 (by decide) (by decide),
    target_run true true 2 1 (by decide) (by decide)⟩

theorem zero_horizon (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    (Source.execS (globals p) frame 0 0 none statement (locals left right x y hx hy)).run
      (Source.L0 E,original) = (.error .timeout,(Source.L0 E,original)) := rfl

theorem one_horizon (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    (Source.execS (globals p) frame 1 0 none statement (locals left right x y hx hy)).run
      (Source.L0 E,original) = (.error .timeout,(Source.L0 E,original)) := rfl

theorem empty_block_selected : compile (C:=C) maps 0 fragment
    (.block .nil : Source.RStmt E [] false .body SrcCtx SrcCtx) = some [] := rfl

theorem bare_guard_refused : compile (C:=C) maps 0 fragment localInput = none := rfl

theorem skip_body_refused : compile (C:=C) maps 0 fragment
    (.block (.stmt .skip .nil) : Source.RStmt E [] false .body SrcCtx SrcCtx) = none := rfl

theorem unchecked_body_refused : compile (C:=C) maps 0 fragment
    (.block (.unchecked .nil .nil) : Source.RStmt E [] false .body SrcCtx SrcCtx) = none := rfl

theorem growing_body_refused : compile (C:=C) maps 0 fragment
    (.block (.stmt (.declVar .bool) .nil) : Source.RStmt E [] false .body SrcCtx SrcCtx) = none := rfl

theorem assignment_body_refused : compile (C:=C) maps 0 fragment
    (.block (.stmt (.expr (.assign (.local (.here : Source.Idx SrcCtx .bool)) (.bool false))) .nil) :
      Source.RStmt E [] false .body SrcCtx SrcCtx) = none := rfl

#print axioms viewed
#print axioms lowered
#print axioms public_selected
#print axioms public_compilation
#print axioms client
#print axioms source_run
#print axioms target_run
#print axioms success
#print axioms first_failure
#print axioms middle_failure
#print axioms last_failure
#print axioms zero_horizon
#print axioms one_horizon
#print axioms empty_block_selected
#print axioms bare_guard_refused
#print axioms skip_body_refused
#print axioms unchecked_body_refused
#print axioms growing_body_refused
#print axioms assignment_body_refused
end Solidity.Backend.FailurePaths.GuardBlockSelection.Controls
