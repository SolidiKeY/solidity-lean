import Solidity.Backend.FailurePaths.GuardBodySelection
import Solidity.Backend.FailurePaths.GuardSequencesControls

/-! Direct indexed Source-items clients of the structural selector. The
nonempty mixed-context body is passed to the new compiler, with no supplied
statement list or desired execution. Refusals are compiler scope, not Source
invalidity. -/
namespace Solidity.Backend.FailurePaths.GuardBodySelection.Controls
open Evm Evm.Memory CheckedGuards.Controls
open PrimitivePackets.Comparisons

def body : Source.RItems E [] false .body SrcCtx SrcCtx :=
  .stmt localInput (.stmt (logicalInput false) (.stmt (relationalInput .lt) .nil))
def admitted : View body := ⟨rfl,GuardSequences.Controls.inputs,rfl⟩

theorem viewed : view body = some admitted := rfl

theorem public_selected : compile (C:=C) maps 0 fragment body = some GuardSequences.Controls.code := by
  simp only [compile,viewed,bind,Option.bind]
  exact GuardSequences.Controls.public_selected

theorem public_compilation : ∃ (witness : View body) (target : Prog C TgtCtx TgtCtx)
    (checked : CompiledProg 0 fragment target),
    view body = some witness ∧ GuardSequences.lower maps witness.statements = some target ∧
    Memory.compileProg 0 fragment target = some checked ∧ checked.frag = fragment ∧
    checked.code = GuardSequences.Controls.code :=
  selected_public maps 0 fragment body GuardSequences.Controls.code public_selected

theorem client (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    ∃ value : Bool,
      (Source.execItems (globals p) frame 10 0 none body (locals left right x y hx hy)).run
        (Source.L0 E,original) =
        (if value then (.ok (.normal (locals left right x y hx hy)),(Source.L0 E,original))
         else (.error (.revert []),(Source.L0 E,original))) ∧
      run GuardSequences.Controls.code (machine left right x y hx hy) =
        (if value then .ok (machine left right x y hx hy) 0 else .revert) := by
  obtain ⟨witness,value,chosen,source,target⟩ := selected_correct maps 0 fragment body
    GuardSequences.Controls.code public_selected (globals p) frame 0
    (locals left right x y hx hy) original (state left right x y hx hy)
    (related left right x y hx hy) (represented left right x y hx hy)
  rw [viewed] at chosen
  cases Option.some.inj chosen
  exact ⟨value,source,target⟩

theorem source_run (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    (Source.execItems (globals p) frame 10 0 none body (locals left right x y hx hy)).run
      (Source.L0 E,original) =
      if left && (left && right) && decide (x < y)
      then (.ok (.normal (locals left right x y hx hy)),(Source.L0 E,original))
      else (.error (.revert []),(Source.L0 E,original)) :=
  GuardSequences.Controls.source_run p left right x y hx hy

theorem target_run (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    run GuardSequences.Controls.code (machine left right x y hx hy) =
      if left && (left && right) && decide (x < y)
      then .ok (machine left right x y hx hy) 0 else .revert :=
  GuardSequences.Controls.target_run left right x y hx hy

theorem zero_horizon (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi)
    (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    (Source.execItems (globals p) frame 0 0 none body (locals left right x y hx hy)).run
      (Source.L0 E,original) = (.error .timeout,(Source.L0 E,original)) := rfl

theorem empty_selected : compile (E:=E) (C:=C) maps 0 fragment .nil = some [] := rfl

theorem skip_refused : compile (C:=C) maps 0 fragment
    (.stmt (.skip : Source.RStmt E [] false .body SrcCtx SrcCtx) .nil) = none := rfl

theorem unchecked_refused : compile (C:=C) maps 0 fragment
    (.unchecked .nil .nil : Source.RItems E [] false .body SrcCtx SrcCtx) = none := rfl

theorem assignment_refused : compile (E:=E) (C:=C) maps 0 fragment
    (.stmt (.expr (.assign (.local (.here : Source.Idx SrcCtx .bool)) (.bool false))) .nil) = none := rfl

theorem literal_guard_refused : compile (C:=C) maps 0 fragment
    (.stmt localInput (.stmt (.expr (.builtin .require (.cons (.bool false) .nil) rfl)) .nil)) = none := rfl

theorem growing_context_refused :
    view (.stmt (.declVar .bool) .nil : Source.RItems E [] false .body SrcCtx (.bool :: SrcCtx)) = none := rfl

#print axioms viewed
#print axioms public_selected
#print axioms public_compilation
#print axioms client
#print axioms source_run
#print axioms target_run
#print axioms zero_horizon
#print axioms empty_selected
#print axioms skip_refused
#print axioms unchecked_refused
#print axioms assignment_refused
#print axioms literal_guard_refused
#print axioms growing_context_refused
end Solidity.Backend.FailurePaths.GuardBodySelection.Controls
