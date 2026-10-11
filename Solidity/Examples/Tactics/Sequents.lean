import Solidity.Calculus.Sequents

/-!
# Checked sequent lines on scoped goals, pinned

`Calculus/Sequents.lean`: under `open scoped Solidity.Scoped`,
`show sequent!{ Γ ⟹ φ }` checks that a scoped goal prints as the line
(its erasure against the line read as today's), as a walk over today's
goals states them (today's `Calculus/Sequents`).  A block's `}` is not
written; a hidden binder is no entry, and an entry folded into the formula
is not the line.
-/

namespace Solidity.Examples.Tactics.Sequents

open Solidity

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-- A walk, its goals checked lines; a wrong line fails. -/
example : ⊢ dl!{ [ if (true) { x = 2; } else { x = 1; }; ] true } := by
  apply Proves.allIntro
  show sequent!{ ∀ uint x ⟹ [ if (true) { x = 2; } else { x = 1; }; ] true }
  apply Proves.split (Taclet.toStep .ifElseSplit)
  case thn =>
    show sequent!{ ∀ uint x, true ≐ true ⟹ [ x = 2; ] true }
    -- an entry folded into the formula is not the line
    fail_if_success show_sequent!{ ⟹ ∀ uint x; true ≐ true → [ x = 2; ] true }
    apply Proves.update (Taclet.toStep .localValueAssign)
    fail_if_success show sequent!{ ∀ uint x, true ≐ true, { x := 1 } ⟹ true }
    show sequent!{ ∀ uint x, true ≐ true, { x := 2 } ⟹ true }
    exact .updIntro (.closeTrue rfl)
  case els =>
    apply Proves.update (Taclet.toStep .localValueAssign)
    show sequent!{ ∀ uint x, true ≐ false, { x := 1 } ⟹ true }
    exact .updIntro (.closeTrue rfl)

/-- A capture's fresh name, and a hidden binder that is no entry. -/
example : ⊢ dl!{ [ uint to = 9; to.transfer(x + 2); ] true } := by
  apply Proves.allIntro
  apply Proves.bind (Taclet.toStep .localValueDeclInitDrop)
  apply Proves.update (Taclet.toStep .localValueAssign)
  show sequent!{ ∀ uint x, { to := 9 } ⟹ [ to.transfer(x + 2); ] true }
  apply Proves.unfold (Taclet.toStep .transfer_unfold_rightSndArgument)
  show sequent!{ ∀ uint x, { to := 9 } ⟹ [ uint se1 = x + 2; to.transfer(se1); ] true }
  apply Proves.bind (Taclet.toStep .localValueDeclInitDrop)
  apply Proves.update (Taclet.toStep .binopAssignment)
  show sequent!{ ∀ uint x, { to := 9 }, { se1 := x + 2 } ⟹ [ to.transfer(se1); ] true }
  apply Proves.update (Taclet.toStep .transferNoCallbackBox)
  exact .updIntro (.closeTrue rfl)

end Solidity.Examples.Tactics.Sequents
