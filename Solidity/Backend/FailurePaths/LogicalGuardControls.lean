import Solidity.Backend.FailurePaths.LogicalGuard
import Solidity.Backend.FailurePaths.Statements
import Solidity.Backend.PrimitivePackets.Comparisons.Controls

/-! Inhabited Boolean-local logical guards in either Source pipeline. The
poisoned-right controls below are separate target-only execution checks, not
inputs satisfying StateRepr or additional Source correspondence claims. -/
namespace Solidity.Backend.FailurePaths.LogicalGuard.Controls
open Evm Evm.Memory

def locals (x y : Bool) : Source.Locals PrimitivePackets.Comparisons.Controls.E.layout [.bool,.bool] :=
  .cons (.bool x) (.cons (.bool y) .nil)
def state (x y : Bool) :=
  (PrimitivePackets.Comparisons.Controls.initial.push (t:=.val .bool) y).push (t:=.val .bool) x
def machine (x y : Bool) :=
  writeMachine (writeMachine PrimitivePackets.Comparisons.Controls.machine0 (cell 0) (.val (bword y)))
    (cell 1) (.val (bword x))
def fragment := (Frag.init []).push (.val .bool) .ok |>.push (.val .bool) .ok

theorem represented (x y : Bool) :
    StateRepr 1 0 4 fragment (state x y) PrimitivePackets.Comparisons.Controls.addresses (machine x y) :=
  (PrimitivePackets.Comparisons.Controls.initial_repr.consVal (p:=.bool) y (.val (bword y)) rfl (by decide)).consVal
    (p:=.bool) x (.val (bword x)) rfl (by change 2 ≤ 4; decide)

def Check (p : Roadmap.Pipeline) (disjunction x y : Bool) : Prop :=
  StateRepr 1 0 4 fragment (state x y) PrimitivePackets.Comparisons.Controls.addresses (machine x y) ∧
  (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame
      7 0 none (statement disjunction .here (.there .here)) (locals x y)).run
      (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
    (if result disjunction x y then (.ok (.normal (locals x y)),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))
     else (.error (.revert []),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))) ∧
  compileStmt 0 fragment (target (C:=PrimitivePackets.Comparisons.Controls.C) disjunction .here (.there .here)) =
    some (selected 0 fragment disjunction .here (.there .here)) ∧
  run (selected (C:=PrimitivePackets.Comparisons.Controls.C) 0 fragment disjunction .here (.there .here)).code
      (machine x y) = (if result disjunction x y then .ok (machine x y) 0 else .revert)

theorem checked (p : Roadmap.Pipeline) (disjunction x y : Bool) : Check p disjunction x y :=
  ⟨represented x y,agreement (PrimitivePackets.Comparisons.Controls.global p)
    PrimitivePackets.Comparisons.Controls.frame 0 (locals x y)
    PrimitivePackets.Comparisons.Controls.sourceState (state x y)
    disjunction .here (.there .here) .here (.there .here) x y rfl rfl rfl rfl (represented x y)⟩

theorem conjunction (p : Roadmap.Pipeline) (x y : Bool) : Check p false x y := checked p false x y
theorem disjunction (p : Roadmap.Pipeline) (x y : Bool) : Check p true x y := checked p true x y

theorem true_or_false (p : Roadmap.Pipeline) :
    run (selected (C:=PrimitivePackets.Comparisons.Controls.C) 0 fragment true .here (.there .here)).code
      (machine true false) = .ok (machine true false) 0 := (checked p true true false).2.2.2

theorem false_and_true (p : Roadmap.Pipeline) :
    run (selected (C:=PrimitivePackets.Comparisons.Controls.C) 0 fragment false .here (.there .here)).code
      (machine false true) = .revert := (checked p false false true).2.2.2

/-- Intentionally outside StateRepr: the second Boolean cell contains a slot. -/
def poisoned (x : Bool) : Machine := writeMachine (machine x false) (cell 0) (.slot (.root 9))

theorem poison_right_faults (x : Bool) :
    run ([.mload (cell 0)] ++ assertTop) (poisoned x) = .fault := rfl

theorem poison_right_not_revert (x : Bool) :
    run ([.mload (cell 0)] ++ assertTop) (poisoned x) ≠ .revert := by
  rw [poison_right_faults]
  intro h
  cases h

theorem or_skips_poisoned_right :
    run (selected (C:=PrimitivePackets.Comparisons.Controls.C) 0 fragment true .here (.there .here)).code
      (poisoned true) = .ok (poisoned true) 0 := rfl

theorem and_skips_poisoned_right :
    run (condition (C:=PrimitivePackets.Comparisons.Controls.C) 0 fragment false .here (.there .here)).code
      (poisoned false) = .ok ((poisoned false).push (.val (bword false))) 0 := rfl

theorem old_selector_refuses (p : Roadmap.Pipeline) (disjunction : Bool) :
    compileStatement (PrimitivePackets.Comparisons.Controls.global p) 0
      (statement (Γ:=[.bool,.bool]) disjunction .here (.there .here)) = none := rfl

theorem zero_horizon (p : Roadmap.Pipeline) :
    (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame
      0 0 none (statement false .here (.there .here)) (locals true true)).run
      (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
      (.error .timeout,(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState)) := rfl

theorem saved_tail (x y : Bool) : (machine x y).stack = [w[77]] := rfl

/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.represented' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms represented
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checked
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.conjunction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms conjunction
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.disjunction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms disjunction
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.true_or_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms true_or_false
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.false_and_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms false_and_true
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.poison_right_faults' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms poison_right_faults
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.poison_right_not_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms poison_right_not_revert
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.or_skips_poisoned_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms or_skips_poisoned_right
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.and_skips_poisoned_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms and_skips_poisoned_right
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.old_selector_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms old_selector_refuses
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.Controls.zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms zero_horizon
end Solidity.Backend.FailurePaths.LogicalGuard.Controls
