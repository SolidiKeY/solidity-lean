import Solidity.Backend.FailurePaths.GuardSequences
import Solidity.Backend.FailurePaths.GuardLoweringControls

/-! Inhabited finite-sequence clients in the mixed Boolean/integer layout,
with exact public-selected instruction concatenation, both Source pipelines,
first/later failures and refusal of an unsupported statement at any position. -/
namespace Solidity.Backend.FailurePaths.GuardSequences.Controls
open Evm Evm.Memory CheckedGuards.Controls
open GuardLowering.Controls
open PrimitivePackets.Comparisons

def inputs : List (Source.RStmt E [] false .body SrcCtx SrcCtx) :=
  [localInput,logicalInput false,relationalInput .lt]
def target : Prog C TgtCtx TgtCtx :=
  .cons localTarget (.cons (logicalTarget false) (.cons (relationalTarget .lt) .nil))
def code : List Evm.Instr := localCode ++ (logicalCode false ++ (relationalCode .lt ++ []))

theorem lowered : lower (C:=C) maps inputs = some target := rfl

theorem public_selected : compile (C:=C) maps 0 fragment inputs = some code := by
  simp only [compile,lowered,bind,Option.bind,pure]
  rfl

theorem public_compilation : ∃ checked : CompiledProg 0 fragment target,
    Memory.compileProg 0 fragment target = some checked ∧ checked.frag = fragment :=
  lowered_public maps 0 fragment inputs target lowered

theorem client (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    ∃ value : Bool,
      (Source.execItems (globals p) frame 10 0 none (items inputs) (locals left right x y hx hy)).run
        (Source.L0 E,original) =
        (if value then (.ok (.normal (locals left right x y hx hy)),(Source.L0 E,original))
         else (.error (.revert []),(Source.L0 E,original))) ∧
      run code (machine left right x y hx hy) =
        (if value then .ok (machine left right x y hx hy) 0 else .revert) :=
  selected_correct maps 0 fragment inputs code public_selected (globals p) frame 0
    (locals left right x y hx hy) original (state left right x y hx hy)
    (related left right x y hx hy) (represented left right x y hx hy)

/-- General complete-machine observation, proved by the three checked leaf
simulations rather than evaluating equality on function-valued memory. -/
theorem target_run (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    run code (machine left right x y hx hy) =
      if left && (left && right) && decide (x < y)
      then .ok (machine left right x y hx hy) 0 else .revert := by
  have first := RuntimeGuard.selected_run (state left right x y hx hy) (.here) left rfl
    (represented left right x y hx hy)
  have second := LogicalGuard.selected_run (state left right x y hx hy) false .here (.there .here)
    left right rfl rfl (represented left right x y hx hy)
  have third := relational_less left right x y hx hy
  change run localCode (machine left right x y hx hy) = _ at first
  change run (logicalCode false) (machine left right x y hx hy) =
    (if left && right then .ok (machine left right x y hx hy) 0 else .revert) at second
  unfold code
  cases left with
  | false => exact run_append_revert first
  | true =>
    rw [run_append_skip first]
    change run (logicalCode false ++ (relationalCode .lt ++ [])) _ = _
    cases right with
    | false => exact run_append_revert second
    | true =>
      rw [run_append_skip second]
      change run (relationalCode .lt ++ []) _ = _
      simpa only [List.append_nil] using third

theorem source_run (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    (Source.execItems (globals p) frame 10 0 none (items inputs) (locals left right x y hx hy)).run
      (Source.L0 E,original) =
      if left && (left && right) && decide (x < y)
      then (.ok (.normal (locals left right x y hx hy)),(Source.L0 E,original))
      else (.error (.revert []),(Source.L0 E,original)) := by
  obtain ⟨value,source,target⟩ := client p left right x y hx hy
  rw [target_run] at target
  cases value <;> cases actual : (left && (left && right) && decide (x < y)) <;>
    simp only [actual,Bool.false_eq_true,if_false,if_true,reduceCtorEq] at target source ⊢
  all_goals exact source

theorem zero_horizon (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    (Source.execItems (globals p) frame 0 0 none (items inputs) (locals left right x y hx hy)).run
      (Source.L0 E,original) = (.error .timeout,(Source.L0 E,original)) := rfl

-- Concrete observations retain the complete machine, including its saved stack.
theorem success : run code (machine true true 1 2 (by decide) (by decide)) =
    .ok (machine true true 1 2 (by decide) (by decide)) 0 := target_run _ _ _ _ _ _
theorem first_failure : run code (machine false true 1 2 (by decide) (by decide)) = .revert := target_run _ _ _ _ _ _
theorem middle_failure : run code (machine true false 1 2 (by decide) (by decide)) = .revert := target_run _ _ _ _ _ _
theorem last_failure : run code (machine true true 2 1 (by decide) (by decide)) = .revert := target_run _ _ _ _ _ _
theorem equality_failure : run code (machine true true 2 2 (by decide) (by decide)) = .revert := target_run _ _ _ _ _ _

theorem empty_selected : compile (E:=E) (C:=C) maps 0 fragment [] = some [] := rfl

theorem unsupported_tail : lower (C:=C) maps [localInput,(.expr (.builtin .require (.cons (.bool false) .nil) rfl))] = none := rfl

theorem unsupported_compile : compile (C:=C) maps 0 fragment
    [localInput,(.expr (.builtin .require (.cons (.bool false) .nil) rfl))] = none := rfl

#print axioms unsupported_compile
#print axioms lowered
#print axioms public_selected
#print axioms public_compilation
#print axioms client
#print axioms source_run
#print axioms zero_horizon
#print axioms target_run
#print axioms success
#print axioms first_failure
#print axioms middle_failure
#print axioms last_failure
#print axioms equality_failure
#print axioms empty_selected
#print axioms unsupported_tail
end Solidity.Backend.FailurePaths.GuardSequences.Controls
