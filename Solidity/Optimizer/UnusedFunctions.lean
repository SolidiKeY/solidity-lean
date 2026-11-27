import Solidity.Optimizer.Pass
import Solidity.Yul.OpenRun

namespace Solidity.Optimizer.UnusedFunctions
open Solidity.Yul
variable {F : List Sig} {X : List ExternalType} {c : Control} {n : Nat}

def isSkip (code : Solidity.Yul.Stmt F X c n) : Bool := by
  apply Solidity.Yul.Stmt.casesOn (motive_1 := fun _ _ _ _ _ => Bool) code
  case skip => intros; exact true
  all_goals intros; exact false

def isIdleGroup (code : Solidity.Yul.Stmt F X c n) : Bool := by
  apply Solidity.Yul.Stmt.casesOn (motive_1 := fun _ _ _ _ _ => Bool) code
  case functions => intro F X c n signatures bodies rest; exact isSkip rest
  all_goals intros; exact false

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

theorem prune_policy {code : Solidity.Yul.Stmt F X c n} (h : Policy.StmtP .A code) :
    Policy.StmtP .A (pruneIdleGroup code) := by
  unfold pruneIdleGroup
  split
  · exact True.intro
  · exact h

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

theorem idle_group_horizon_one (environment : OpenFunctions.PureEnvironment F)
    (signatures : List Sig)
    (bodies : Bodies (signatures ++ F) (globals X) signatures)
    (policy : Policy.StmtP .A (.functions signatures bodies (.skip :
      Solidity.Yul.Stmt (signatures ++ F) X c n))) (state : WordState X n) :
    OpenRun.statement 1 environment (.functions signatures bodies .skip) policy state = none ∧
    OpenRun.statement 1 environment (pruneIdleGroup (.functions signatures bodies .skip))
      (prune_policy policy) state = some ⟨state, .normal⟩ := ⟨rfl, rfl⟩

end Solidity.Optimizer.UnusedFunctions
