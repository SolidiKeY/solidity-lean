import Solidity.Calculus.Core.Derive
import Solidity.Calculus.Core.Notation
import Solidity.Calculus.Core.Delab

/-!
# The scoped strategy tools

The tactics of `Calculus/Core/Symex.lean` and `Calculus/Core/Derive.lean`
on scoped goals `Core.Valid φ` (`cdl!{ … }`): `sol_symex` then `sol_close`,
`sol_prove` as one kernel evaluation, and `sol_derive?`'s walk, one
`refine` per rule cited by its taclet, each leaf closed (`Proves.close`
and today's closer on its erasure), pinned and replayed.
-/

namespace Solidity.Examples.Tactics.CoreDerive

open Solidity

local instance : InContract := ⟨StandardExample⟩

example : Core.Valid cdl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 } := by
  sol_prove

example : Core.Valid cdl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 } := by
  sol_symex
  sol_close

example : Core.Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] total != 0 } := by
  sol_prove

/--
info: Try this:
  refine Core.Proves.valid (R := RuleSet.all) ?_
    refine Core.Proves.allIntro ?_
    apply Core.Proves.bind (Core.Taclet.step_eq .localValueDeclInitDrop)
    apply Core.Proves.update (Core.Taclet.step_eq .binopAssignment)
    apply Core.Proves.unfold (Core.Taclet.step_eq .ifElseUnfold)
    apply Core.Proves.bind (Core.Taclet.step_eq .localValueDeclInitDrop)
    apply Core.Proves.update (Core.Taclet.step_eq .binopAssignment)
    apply Core.Proves.split (Core.Taclet.step_eq .ifElseSplit)
    case thn =>
      apply Core.Proves.update (Core.Taclet.step_eq .storageRootWriteStore)
      refine Core.Proves.updIntro ?_
      refine Core.Proves.updIntro ?_
      exact Core.Proves.closeTrue rfl
    case els =>
      apply Core.Proves.update (Core.Taclet.step_eq .storageRootWriteStore)
      refine Core.Proves.updIntro ?_
      refine Core.Proves.updIntro ?_
      exact Core.Proves.closeTrue rfl
-/
#guard_msgs in
example : Core.Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] true } := by
  sol_derive?

/-- The suggestion replayed. -/
example : Core.Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] true } := by
  refine Core.Proves.valid (R := RuleSet.all) ?_
  refine Core.Proves.allIntro ?_
  apply Core.Proves.bind (Core.Taclet.step_eq .localValueDeclInitDrop)
  apply Core.Proves.update (Core.Taclet.step_eq .binopAssignment)
  apply Core.Proves.unfold (Core.Taclet.step_eq .ifElseUnfold)
  apply Core.Proves.bind (Core.Taclet.step_eq .localValueDeclInitDrop)
  apply Core.Proves.update (Core.Taclet.step_eq .binopAssignment)
  apply Core.Proves.split (Core.Taclet.step_eq .ifElseSplit)
  case thn =>
    apply Core.Proves.update (Core.Taclet.step_eq .storageRootWriteStore)
    refine Core.Proves.updIntro ?_
    refine Core.Proves.updIntro ?_
    exact Core.Proves.closeTrue rfl
  case els =>
    apply Core.Proves.update (Core.Taclet.step_eq .storageRootWriteStore)
    refine Core.Proves.updIntro ?_
    refine Core.Proves.updIntro ?_
    exact Core.Proves.closeTrue rfl

example : Core.Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] true } := by
  sol_derive

/-! A leaf with a formula left closes as today's does: `Proves.close` on its
erasure, then `sol_symex; sol_close`. -/

/--
info: Try this:
  refine Core.Proves.valid (R := RuleSet.all) ?_
    refine Core.Proves.allIntro ?_
    apply Core.Proves.bind (Core.Taclet.step_eq .localValueDeclInitDrop)
    apply Core.Proves.update (Core.Taclet.step_eq .binopAssignment)
    apply Core.Proves.unfold (Core.Taclet.step_eq .ifElseUnfold)
    apply Core.Proves.bind (Core.Taclet.step_eq .localValueDeclInitDrop)
    apply Core.Proves.update (Core.Taclet.step_eq .binopAssignment)
    apply Core.Proves.split (Core.Taclet.step_eq .ifElseSplit)
    case thn =>
      apply Core.Proves.update (Core.Taclet.step_eq .storageRootWriteStore)
      refine Core.Proves.updIntro ?_
      refine Core.Proves.updIntro ?_
      refine Core.Proves.close [] rfl List.nodup_nil ?_
      sol_symex
      sol_close
    case els =>
      apply Core.Proves.update (Core.Taclet.step_eq .storageRootWriteStore)
      refine Core.Proves.updIntro ?_
      refine Core.Proves.updIntro ?_
      refine Core.Proves.close [] rfl List.nodup_nil ?_
      sol_symex
      sol_close
-/
#guard_msgs in
example : Core.Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] total != 0 } := by
  sol_derive?

/-- The suggestion replayed. -/
example : Core.Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] total != 0 } := by
  refine Core.Proves.valid (R := RuleSet.all) ?_
  refine Core.Proves.allIntro ?_
  apply Core.Proves.bind (Core.Taclet.step_eq .localValueDeclInitDrop)
  apply Core.Proves.update (Core.Taclet.step_eq .binopAssignment)
  apply Core.Proves.unfold (Core.Taclet.step_eq .ifElseUnfold)
  apply Core.Proves.bind (Core.Taclet.step_eq .localValueDeclInitDrop)
  apply Core.Proves.update (Core.Taclet.step_eq .binopAssignment)
  apply Core.Proves.split (Core.Taclet.step_eq .ifElseSplit)
  case thn =>
    apply Core.Proves.update (Core.Taclet.step_eq .storageRootWriteStore)
    refine Core.Proves.updIntro ?_
    refine Core.Proves.updIntro ?_
    refine Core.Proves.close [] rfl List.nodup_nil ?_
    sol_symex
    sol_close
  case els =>
    apply Core.Proves.update (Core.Taclet.step_eq .storageRootWriteStore)
    refine Core.Proves.updIntro ?_
    refine Core.Proves.updIntro ?_
    refine Core.Proves.close [] rfl List.nodup_nil ?_
    sol_symex
    sol_close

/-- `sol_derive` leaves the leaves, as today's does. -/
example : Core.Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] total != 0 } := by
  sol_derive
  all_goals
    refine Core.Proves.close [] rfl List.nodup_nil ?_
    sol_symex
    sol_close

/-! Today's `sol_derive` on today's goal, the scoped one beside it. -/

example : ⊨ dl!{ [ x = 2; ] x == 2 } := by
  apply Proves.valid
  sol_derive
  refine Proves.close ?_
  sol_symex
  sol_close

end Solidity.Examples.Tactics.CoreDerive
