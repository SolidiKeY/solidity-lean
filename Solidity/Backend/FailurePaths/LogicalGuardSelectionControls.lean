import Solidity.Backend.FailurePaths.LogicalGuardSelection
import Solidity.Backend.FailurePaths.LogicalGuardControls

/-! Inhabited Source selector consumers with both pipelines/operators and all
Boolean inputs. Context correspondence is explicit and populated; these are
indexed Source controls, not a whole-program context-map producer. -/
namespace Solidity.Backend.FailurePaths.LogicalGuardSelection.Controls
open Evm Evm.Memory

def map : Source.Idx [.bool,.bool] .bool → Idx [.val .bool,.val .bool] (.val .bool)
  | .here => .here
  | .there .here => .there .here
  | .there (.there i) => nomatch i

def input (disjunction : Bool) :
    Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body [.bool,.bool] [.bool,.bool] :=
  LogicalGuard.statement disjunction .here (.there .here)

def code (disjunction : Bool) : List Evm.Instr :=
  (LogicalGuard.selected (C:=PrimitivePackets.Comparisons.Controls.C) 0 LogicalGuard.Controls.fragment
    disjunction .here (.there .here)).code

theorem selected (disjunction : Bool) : compile (C:=PrimitivePackets.Comparisons.Controls.C) map 0
    LogicalGuard.Controls.fragment (input disjunction) = some (code disjunction) :=
  accepts_logical map 0 _ disjunction .here (.there .here)

theorem local_relation (x y : Bool) : ∀ (i : Source.Idx [.bool,.bool] .bool) (value : Bool),
    (LogicalGuard.Controls.locals x y).get i = .bool value →
      TEnv.get (map i) (LogicalGuard.Controls.state x y).env = value := by
  intro i value read
  cases i with
  | here => cases read; rfl
  | there i =>
    cases i with
    | here => cases read; rfl
    | there i => nomatch i

theorem success_client (p : Roadmap.Pipeline) (disjunction x y : Bool) :
    ∃ (chosen : Bool) (a b : Source.Idx [.bool,.bool] .bool) (left right : Bool),
      (LogicalGuard.Controls.locals x y).get a = .bool left ∧
      (LogicalGuard.Controls.locals x y).get b = .bool right ∧
      compileStmt 0 LogicalGuard.Controls.fragment
        (LogicalGuard.target (C:=PrimitivePackets.Comparisons.Controls.C) chosen (map a) (map b)) =
          some (LogicalGuard.selected 0 LogicalGuard.Controls.fragment chosen (map a) (map b)) ∧
      (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame
        7 0 none (input disjunction) (LogicalGuard.Controls.locals x y)).run
        (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
        (if LogicalGuard.result chosen left right then
          (.ok (.normal (LogicalGuard.Controls.locals x y)),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))
         else (.error (.revert []),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))) ∧
      run (code disjunction) (LogicalGuard.Controls.machine x y) =
        (if LogicalGuard.result chosen left right then .ok (LogicalGuard.Controls.machine x y) 0 else .revert) :=
  selected_correct map 0 LogicalGuard.Controls.fragment (input disjunction) (code disjunction) (selected disjunction)
    (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame 0
    (LogicalGuard.Controls.locals x y) PrimitivePackets.Comparisons.Controls.sourceState
    (LogicalGuard.Controls.state x y) (local_relation x y) (LogicalGuard.Controls.represented x y)

theorem observations (p : Roadmap.Pipeline) (disjunction x y : Bool) :
    StateRepr 1 0 4 LogicalGuard.Controls.fragment (LogicalGuard.Controls.state x y)
      PrimitivePackets.Comparisons.Controls.addresses (LogicalGuard.Controls.machine x y) ∧
    compile (C:=PrimitivePackets.Comparisons.Controls.C) map 0 LogicalGuard.Controls.fragment
      (input disjunction) = some (code disjunction) ∧
    (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame
      7 0 none (input disjunction) (LogicalGuard.Controls.locals x y)).run
      (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
      (if LogicalGuard.result disjunction x y then
        (.ok (.normal (LogicalGuard.Controls.locals x y)),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))
       else (.error (.revert []),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))) ∧
    run (code disjunction) (LogicalGuard.Controls.machine x y) =
      (if LogicalGuard.result disjunction x y then .ok (LogicalGuard.Controls.machine x y) 0 else .revert) :=
  ⟨LogicalGuard.Controls.represented x y,selected disjunction,
    (LogicalGuard.Controls.checked p disjunction x y).2.1,
    (LogicalGuard.Controls.checked p disjunction x y).2.2.2⟩

theorem true_or_false (p : Roadmap.Pipeline) :
    run (code true) (LogicalGuard.Controls.machine true false) =
      .ok (LogicalGuard.Controls.machine true false) 0 := (observations p true true false).2.2.2

theorem false_and_true (p : Roadmap.Pipeline) :
    run (code false) (LogicalGuard.Controls.machine false true) = .revert :=
  (observations p false false true).2.2.2

theorem local_only_refused : compile (C:=PrimitivePackets.Comparisons.Controls.C) map 0 LogicalGuard.Controls.fragment
    (RuntimeGuard.statement (E:=PrimitivePackets.Comparisons.Controls.E) .here) = none := rfl

theorem literal_operand_refused : compile (C:=PrimitivePackets.Comparisons.Controls.C) map 0 LogicalGuard.Controls.fragment
    (.expr (.builtin .require (.cons (.binary .and (.bool true) (.local .here)) .nil) rfl) :
      Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body [.bool,.bool] [.bool,.bool]) = none := rfl

theorem assert_refused (disjunction : Bool) : compile (C:=PrimitivePackets.Comparisons.Controls.C) map 0 LogicalGuard.Controls.fragment
    (.expr (.builtin .assert (.cons (LogicalGuard.expression disjunction .here (.there .here)) .nil) rfl) :
      Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body [.bool,.bool] [.bool,.bool]) = none := rfl

theorem message_refused (disjunction : Bool) : compile (C:=PrimitivePackets.Comparisons.Controls.C) map 0 LogicalGuard.Controls.fragment
    (.expr (.builtin .require (.cons (LogicalGuard.expression disjunction .here (.there .here))
      (.cons (.str [1]) .nil)) rfl) :
      Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body [.bool,.bool] [.bool,.bool]) = none := rfl

theorem wrong_relation : ¬ (∀ (i : Source.Idx [.bool,.bool] .bool) (value : Bool),
    (LogicalGuard.Controls.locals true false).get i = .bool value →
      TEnv.get (map i) (LogicalGuard.Controls.state false false).env = value) := by
  intro relation
  have bad := relation .here true rfl
  cases bad

theorem zero_horizon (p : Roadmap.Pipeline) (disjunction x y : Bool) :
    (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame
      0 0 none (input disjunction) (LogicalGuard.Controls.locals x y)).run
      (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
      (.error .timeout,(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState)) := rfl

#print axioms selected
#print axioms local_relation
#print axioms success_client
#print axioms observations
#print axioms true_or_false
#print axioms false_and_true
#print axioms local_only_refused
#print axioms literal_operand_refused
#print axioms assert_refused
#print axioms message_refused
#print axioms wrong_relation
#print axioms zero_horizon
end Solidity.Backend.FailurePaths.LogicalGuardSelection.Controls
