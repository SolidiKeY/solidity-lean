import Solidity.Optimizer.Pass
import Solidity.Yul.OpenRun

/-! Conservative unused-group pruning. An immediate functions-group whose
continuation is skip cannot invoke its declarations. Every other input is kept.
The execution results below concern the existing tier-A runner, not D6, source
admission, physical code or gas. Horizon exhaustion is not a semantic failure. -/
namespace Solidity.Optimizer.UnusedFunctions
open Solidity.Yul
variable {F : List Sig} {X : List ExternalType} {c : Control} {n : Nat}

/-- Recognize skip without matching an indexed family in evaluated code. -/
def isSkip (code : Solidity.Yul.Stmt F X c n) : Bool := by
  apply Solidity.Yul.Stmt.casesOn (motive_1 := fun _ _ _ _ _ => Bool) code
  case skip => intros; exact true
  all_goals intros; exact false

/-- Only an immediate group with a skip continuation is selected. -/
def isIdleGroup (code : Solidity.Yul.Stmt F X c n) : Bool := by
  apply Solidity.Yul.Stmt.casesOn (motive_1 := fun _ _ _ _ _ => Bool) code
  case functions => intro F X c n signatures bodies rest; exact isSkip rest
  all_goals intros; exact false

/-- A total intrinsically typed pass; unsupported forms retain their exact AST. -/
def pruneIdleGroup : Solidity.Optimizer.Yul.Pass F X c n :=
  fun code => if isIdleGroup code = true then .skip else code

theorem isSkip_shape {code : Solidity.Yul.Stmt F X c n} (h : isSkip code = true) :
    code = .skip := by
  cases code
  case skip => rfl
  all_goals cases h

theorem idleGroup_shape {code : Solidity.Yul.Stmt F X c n} (h : isIdleGroup code = true) :
    ∃ (signatures : List Sig) (bodies : Bodies (signatures ++ F) (globals X) signatures),
      code = .functions signatures bodies .skip := by
  cases code
  case functions signatures bodies rest =>
    have same : rest = .skip := isSkip_shape h
    subst rest
    exact ⟨signatures, bodies, rfl⟩
  all_goals cases h

/-- Preserve the existing runner's policy; this introduces no admission filter. -/
theorem prune_policy {code : Solidity.Yul.Stmt F X c n} (h : Policy.StmtP .A code) :
    Policy.StmtP .A (pruneIdleGroup code) := by
  unfold pruneIdleGroup
  split
  · exact True.intro
  · exact h

/-- Exact state and control outcome at every horizon large enough for either
form. This is a runner theorem, not a physical-gas theorem. -/
theorem prune_run (fuel : Nat) (environment : OpenFunctions.PureEnvironment F)
    (code : Solidity.Yul.Stmt F X c n) (policy : Policy.StmtP .A code)
    (state : WordState X n) :
    OpenRun.statement (fuel + 2) environment (pruneIdleGroup code)
      (prune_policy policy) state =
    OpenRun.statement (fuel + 2) environment code policy state := by
  by_cases selected : isIdleGroup code = true
  · obtain ⟨signatures, bodies, rfl⟩ := idleGroup_shape selected
    rfl
  · simp only [pruneIdleGroup, if_neg selected]

/-- Completion is preserved even though successful horizons may differ. -/
theorem prune_completion (environment : OpenFunctions.PureEnvironment F)
    (code : Solidity.Yul.Stmt F X c n) (policy : Policy.StmtP .A code)
    (state : WordState X n) (outcome : WordAdapter.Outcome X c n) :
    (∃ fuel, OpenRun.statement fuel environment (pruneIdleGroup code)
      (prune_policy policy) state = some outcome) ↔
    (∃ fuel, OpenRun.statement fuel environment code policy state = some outcome) := by
  by_cases selected : isIdleGroup code = true
  · obtain ⟨signatures, bodies, rfl⟩ := idleGroup_shape selected
    constructor
    · rintro ⟨fuel, completed⟩
      cases fuel with
      | zero => cases completed
      | succ fuel =>
        have same : (some ⟨state, .normal⟩ : Option (WordAdapter.Outcome X c n)) =
            some outcome := completed
        exact ⟨2, same⟩
    · rintro ⟨fuel, completed⟩
      cases fuel with
      | zero => cases completed
      | succ fuel =>
        cases fuel with
        | zero => cases completed
        | succ fuel =>
          have same : (some ⟨state, .normal⟩ : Option (WordAdapter.Outcome X c n)) =
              some outcome := completed
          exact ⟨1, same⟩
  · simp only [pruneIdleGroup, if_neg selected]

/-- Horizon one distinguishes the original group from its pruned form.
Exhausting that horizon is not a source failure or a gas observation. -/
theorem idle_group_horizon_one (environment : OpenFunctions.PureEnvironment F)
    (signatures : List Sig)
    (bodies : Bodies (signatures ++ F) (globals X) signatures)
    (policy : Policy.StmtP .A (.functions signatures bodies (.skip :
      Solidity.Yul.Stmt (signatures ++ F) X c n))) (state : WordState X n) :
    OpenRun.statement 1 environment (.functions signatures bodies .skip) policy state = none ∧
    OpenRun.statement 1 environment (pruneIdleGroup (.functions signatures bodies .skip))
      (prune_policy policy) state = some ⟨state, .normal⟩ := ⟨rfl, rfl⟩

end Solidity.Optimizer.UnusedFunctions
