import Solidity.Optimizer.UnusedFunctions

namespace Solidity.Yul.UnusedFunctionsControls
open Solidity.Optimizer.UnusedFunctions

/-- A genuinely nonempty group with an executable return assignment. -/
def signatures : List Sig := [⟨0, 1⟩]
def bodies : Bodies signatures [] signatures :=
  .cons (.assign (fun _ => .local 0) (.literal (word 7))) .nil

def idle : Stmt [] [.memory] ⟨false, false⟩ 1 :=
  .functions signatures bodies .skip

def idlePolicy : Policy.StmtP .A idle := ⟨⟨⟨fun _ => True.intro, True.intro⟩, True.intro⟩, True.intro⟩

def initial : WordState [.memory] 1 :=
  ⟨fun _ => word 19, fun _ => word 37⟩

/-- Both the nonzero caller local and raw memory-reference cell survive. -/
theorem removes_nonempty : pruneIdleGroup idle = .skip := rfl

theorem preserves_complete_state :
    OpenRun.statement 2 .nil (pruneIdleGroup idle) (prune_policy idlePolicy) initial =
      some ⟨initial, .normal⟩ ∧
    OpenRun.statement 2 .nil idle idlePolicy initial = some ⟨initial, .normal⟩ := ⟨rfl, rfl⟩

theorem horizon_is_not_gas :
    OpenRun.statement 1 .nil idle idlePolicy initial = none ∧
    OpenRun.statement 1 .nil (pruneIdleGroup idle) (prune_policy idlePolicy) initial =
      some ⟨initial, .normal⟩ := idle_group_horizon_one (X := [.memory]) .nil signatures bodies idlePolicy initial

/-- A live invocation retains its group and all original syntax. -/
def live : Stmt [] [.memory] ⟨false, false⟩ 1 :=
  .functions signatures bodies
    (.assign (fun _ => .local 0) (.call .here Fin.elim0))

theorem live_group_retained : pruneIdleGroup live = live := rfl

theorem completion_preserved (outcome : WordAdapter.Outcome [.memory] ⟨false, false⟩ 1) :
    (∃ fuel, OpenRun.statement fuel .nil (pruneIdleGroup idle) (prune_policy idlePolicy)
      initial = some outcome) ↔
    (∃ fuel, OpenRun.statement fuel .nil idle idlePolicy initial = some outcome) :=
  prune_completion .nil idle idlePolicy initial outcome

#print axioms Solidity.Optimizer.UnusedFunctions.isSkip_shape
#print axioms Solidity.Optimizer.UnusedFunctions.idleGroup_shape
#print axioms Solidity.Optimizer.UnusedFunctions.prune_policy
#print axioms Solidity.Optimizer.UnusedFunctions.prune_run
#print axioms Solidity.Optimizer.UnusedFunctions.prune_completion
#print axioms Solidity.Optimizer.UnusedFunctions.idle_group_horizon_one
#print axioms removes_nonempty
#print axioms preserves_complete_state
#print axioms horizon_is_not_gas
#print axioms live_group_retained
#print axioms completion_preserved
end Solidity.Yul.UnusedFunctionsControls
