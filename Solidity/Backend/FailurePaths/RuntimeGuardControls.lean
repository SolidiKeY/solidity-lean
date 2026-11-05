import Solidity.Backend.FailurePaths.RuntimeGuard
import Solidity.Backend.FailurePaths.Statements
import Solidity.Backend.PrimitivePackets.Comparisons.Controls

/-! Inhabited local guards in both Source pipelines, with a saved stack word
and nonempty source log/function-local state. These controls distinguish a
normal guard, empty revert, horizon timeout and assert panic payload. -/
namespace Solidity.Backend.FailurePaths.RuntimeGuard.Controls
open Evm Evm.Memory

def locals (value : Bool) : Source.Locals PrimitivePackets.Comparisons.Controls.E.layout [.bool] :=
  .cons (.bool value) .nil
def state (value : Bool) := PrimitivePackets.Comparisons.Controls.initial.push (t:=.val .bool) value
def machine (value : Bool) := writeMachine PrimitivePackets.Comparisons.Controls.machine0 (cell 0) (.val (bword value))
def fragment := (Frag.init []).push (.val .bool) .ok

theorem represented (value : Bool) :
    StateRepr 1 0 4 fragment (state value) PrimitivePackets.Comparisons.Controls.addresses (machine value) :=
  PrimitivePackets.Comparisons.Controls.initial_repr.consVal (p:=.bool) value (.val (bword value)) rfl (by decide)

def Check (p : Roadmap.Pipeline) (value : Bool) : Prop :=
  StateRepr 1 0 4 fragment (state value) PrimitivePackets.Comparisons.Controls.addresses (machine value) ∧
  (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame 7 0 none (statement .here) (locals value)).run
      (Source.L0 PrimitivePackets.Comparisons.Controls.E,PrimitivePackets.Comparisons.Controls.sourceState) =
    (if value then (.ok (.normal (locals value)),(Source.L0 PrimitivePackets.Comparisons.Controls.E,PrimitivePackets.Comparisons.Controls.sourceState))
     else (.error (.revert []),(Source.L0 PrimitivePackets.Comparisons.Controls.E,PrimitivePackets.Comparisons.Controls.sourceState))) ∧
  compileStmt 0 fragment (target (C:=PrimitivePackets.Comparisons.Controls.C) .here) = some (selected 0 fragment .here) ∧
  run (selected (C:=PrimitivePackets.Comparisons.Controls.C) 0 fragment .here).code (machine value) =
    (if value then .ok (machine value) 0 else .revert)

theorem checked (p : Roadmap.Pipeline) (value : Bool) : Check p value :=
  ⟨represented value,agreement (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame 0 .here .here value
    (locals value) PrimitivePackets.Comparisons.Controls.sourceState (state value) rfl rfl (represented value)⟩

theorem true_guard (p : Roadmap.Pipeline) : Check p true := checked p true
theorem false_guard (p : Roadmap.Pipeline) : Check p false := checked p false

theorem false_not_success (p : Roadmap.Pipeline) :
    (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame 7 0 none (statement .here) (locals false)).run
      (Source.L0 PrimitivePackets.Comparisons.Controls.E,PrimitivePackets.Comparisons.Controls.sourceState) ≠
      (.ok (.normal (locals false)),(Source.L0 PrimitivePackets.Comparisons.Controls.E,PrimitivePackets.Comparisons.Controls.sourceState)) := by
  rw [source_run (value:=false) (read:=rfl)]
  intro h
  cases h

theorem assert_is_not_bare_revert (p : Roadmap.Pipeline) :
    (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame 7 0 none
      (.expr (.builtin .assert (.cons (.local .here) .nil) rfl) :
        Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body [.bool] [.bool]) (locals false)).run
      (Source.L0 PrimitivePackets.Comparisons.Controls.E,PrimitivePackets.Comparisons.Controls.sourceState) =
      (.error (.revert (Source.panicData .assert)),(Source.L0 PrimitivePackets.Comparisons.Controls.E,PrimitivePackets.Comparisons.Controls.sourceState)) := rfl

theorem old_literal_selector_refuses (p : Roadmap.Pipeline) :
    compileStatement (PrimitivePackets.Comparisons.Controls.global p) 0 (statement (Γ:=[.bool]) .here) = none := rfl

theorem saved_tail (value : Bool) : (machine value).stack = [w[77]] := rfl

#print axioms represented
#print axioms checked
#print axioms false_not_success
#print axioms assert_is_not_bare_revert
#print axioms old_literal_selector_refuses
end Solidity.Backend.FailurePaths.RuntimeGuard.Controls
