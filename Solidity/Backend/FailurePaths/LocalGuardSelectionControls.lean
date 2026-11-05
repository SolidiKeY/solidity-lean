import Solidity.Backend.FailurePaths.LocalGuardSelection
import Solidity.Backend.FailurePaths.RuntimeGuardControls

/-! Both pipelines consume the executable selector correctness theorem with
inhabited memory and saved77. Refusals delimit indexed Source input syntax;
a wrong initial local relation is rejected independently of compilation. -/
namespace Solidity.Backend.FailurePaths.LocalGuardSelection.Controls
open Evm Evm.Memory

def map : Source.Idx [.bool] .bool → Idx [.val .bool] (.val .bool)
  | .here => .here
  | .there i => nomatch i

def input : Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body [.bool] [.bool] :=
  RuntimeGuard.statement .here

def code : List Evm.Instr :=
  (RuntimeGuard.selected (C:=PrimitivePackets.Comparisons.Controls.C) 0 RuntimeGuard.Controls.fragment .here).code

theorem selected : compile (C:=PrimitivePackets.Comparisons.Controls.C) map 0
    RuntimeGuard.Controls.fragment input = some code := accepts_local map 0 _ .here

theorem local_relation (value : Bool) : ∀ (i : Source.Idx [.bool] .bool) (v : Bool),
    (RuntimeGuard.Controls.locals value).get i = .bool v →
      TEnv.get (map i) (RuntimeGuard.Controls.state value).env = v := by
  intro i v read
  cases i with
  | here => cases read; rfl
  | there i => nomatch i

theorem observations (p : Roadmap.Pipeline) (value : Bool) :
    StateRepr 1 0 4 RuntimeGuard.Controls.fragment (RuntimeGuard.Controls.state value)
      PrimitivePackets.Comparisons.Controls.addresses (RuntimeGuard.Controls.machine value) ∧
    compile (C:=PrimitivePackets.Comparisons.Controls.C) map 0 RuntimeGuard.Controls.fragment input = some code ∧
    (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame
      7 0 none input (RuntimeGuard.Controls.locals value)).run
      (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
      (if value then (.ok (.normal (RuntimeGuard.Controls.locals value)),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))
       else (.error (.revert []),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))) ∧
    run code (RuntimeGuard.Controls.machine value) =
      (if value then .ok (RuntimeGuard.Controls.machine value) 0 else .revert) := by
  obtain ⟨i,v,read,publicChoice,sourceRun,targetRun⟩ := selected_correct map 0 RuntimeGuard.Controls.fragment
    input code selected (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame 0
    (RuntimeGuard.Controls.locals value) PrimitivePackets.Comparisons.Controls.sourceState
    (RuntimeGuard.Controls.state value) (local_relation value) (RuntimeGuard.Controls.represented value)
  cases i with
  | here =>
      have same : value = v := Source.Val.bool.inj read
      cases same
      exact ⟨RuntimeGuard.Controls.represented value,selected,sourceRun,targetRun⟩
  | there i => nomatch i

theorem literal_refused (value : Bool) :
    compile (C:=PrimitivePackets.Comparisons.Controls.C) map 0 RuntimeGuard.Controls.fragment
      (.expr (.builtin .require (.cons (.bool value) .nil) rfl) :
        Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body [.bool] [.bool]) = none := rfl

theorem assert_refused :
    compile (C:=PrimitivePackets.Comparisons.Controls.C) map 0 RuntimeGuard.Controls.fragment
      (.expr (.builtin .assert (.cons (.local .here) .nil) rfl) :
        Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body [.bool] [.bool]) = none := rfl

theorem message_refused :
    compile (C:=PrimitivePackets.Comparisons.Controls.C) map 0 RuntimeGuard.Controls.fragment
      (.expr (.builtin .require (.cons (.local .here) (.cons (.str [1]) .nil)) rfl) :
        Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body [.bool] [.bool]) = none := rfl

theorem wrong_relation : ¬ (∀ (i : Source.Idx [.bool] .bool) (v : Bool),
    (RuntimeGuard.Controls.locals true).get i = .bool v →
      TEnv.get (map i) (RuntimeGuard.Controls.state false).env = v) := by
  intro related
  have bad := related .here true rfl
  cases bad

theorem zero_horizon (p : Roadmap.Pipeline) (value : Bool) :
    (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame
      0 0 none input (RuntimeGuard.Controls.locals value)).run
      (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
      (.error .timeout,(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState)) := rfl

#print axioms selected
#print axioms local_relation
#print axioms observations
#print axioms literal_refused
#print axioms assert_refused
#print axioms message_refused
#print axioms wrong_relation
#print axioms zero_horizon
end Solidity.Backend.FailurePaths.LocalGuardSelection.Controls
