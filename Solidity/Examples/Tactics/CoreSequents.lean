import Solidity.Calculus.Core.Sequents

/-!
# Checked sequent lines on scoped goals, pinned

`Calculus/Core/Sequents.lean`: under `open scoped Solidity.Core.Scoped`,
`show sequent!{ Γ ⟹ φ }` checks that a scoped goal prints as the line
(its erasure against the line read as today's), as a walk over today's
goals states them (today's `Calculus/Sequents`).  A block's `}` is not
written; a hidden binder is no entry.
-/

namespace Solidity.Examples.Tactics.CoreSequents

open Solidity

local instance : InContract := ⟨StandardExample⟩

open scoped Core.Scoped

/-- A walk, its goals checked lines; a wrong line fails. -/
example : ⊢ dl!{ [ if (true) { x = 2; } else { x = 1; }; ] true } := by
  apply Core.Proves.allIntro
  show sequent!{ ∀ uint x ⟹ [ if (true) { x = 2; } else { x = 1; }; ] true }
  apply Core.Proves.split (Core.Taclet.toStep .ifElseSplit)
  case thn =>
    show sequent!{ ∀ uint x, true ≐ true ⟹ [ x = 2; ] true }
    apply Core.Proves.update (Core.Taclet.toStep .localValueAssign)
    fail_if_success show sequent!{ ∀ uint x, true ≐ true, { x := 1 } ⟹ true }
    show sequent!{ ∀ uint x, true ≐ true, { x := 2 } ⟹ true }
    exact .updIntro (.closeTrue rfl)
  case els =>
    apply Core.Proves.update (Core.Taclet.toStep .localValueAssign)
    show sequent!{ ∀ uint x, true ≐ false, { x := 1 } ⟹ true }
    exact .updIntro (.closeTrue rfl)

/-- A capture's fresh name, and a hidden binder that is no entry. -/
example : ⊢ dl!{ [ uint to = 9; to.transfer(x + 2); ] true } := by
  apply Core.Proves.allIntro
  apply Core.Proves.bind (Core.Taclet.toStep .localValueDeclInitDrop)
  apply Core.Proves.update (Core.Taclet.toStep .localValueAssign)
  show sequent!{ ∀ uint x, { to := 9 } ⟹ [ to.transfer(x + 2); ] true }
  apply Core.Proves.unfold (Core.Taclet.toStep .transfer_unfold_rightSndArgument)
  show sequent!{ ∀ uint x, { to := 9 } ⟹ [ uint se1 = x + 2; to.transfer(se1); ] true }
  apply Core.Proves.bind (Core.Taclet.toStep .localValueDeclInitDrop)
  apply Core.Proves.update (Core.Taclet.toStep .binopAssignment)
  show sequent!{ ∀ uint x, { to := 9 }, { se1 := x + 2 } ⟹ [ to.transfer(se1); ] true }
  apply Core.Proves.update (Core.Taclet.toStep .transferNoCallbackBox)
  exact .updIntro (.closeTrue rfl)

end Solidity.Examples.Tactics.CoreSequents
