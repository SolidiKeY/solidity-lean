import Solidity.Calculus.Core.Derive
import Solidity.Calculus.Core.Notation
import Solidity.Calculus.Core.Delab
import Solidity.Calculus.Core.WalkSyntax
import Solidity.Calculus.Core.ProvesDerive
import Solidity.Calculus.Core.SolkeyProves

/-!
# The scoped strategy tools

The tactics of `Calculus/Core/Symex.lean` and `Calculus/Core/Derive.lean`
on scoped goals `Core.Valid φ` (`cdl!{ … }`): `sol_symex` then `sol_close`,
`sol_prove` as one kernel evaluation, and `sol_derive?`'s walk, one
`refine` per rule cited by its taclet, each leaf closed (`Proves.close`
and today's closer on its erasure), pinned and replayed; `sol_prove` and
a walk under `⊢ₖ`, solkey's rules alone.
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
    refine Core.Proves.allRight ?_
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
  refine Core.Proves.allRight ?_
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
    refine Core.Proves.allRight ?_
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
  refine Core.Proves.allRight ?_
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

/-! ## solkey's rules alone (`⊢ₖ`)

On `Core.Proves C .solkey …` the walk steps with `Stmt.stepIn .solkey`
(`Calculus/Core/ProvesDerive.lean`): on the fragment it fires solkey's
taclets, and each step rule's `hR` is proved by `rule_admits`
(`Stmt.keyStep` by `rfl`). -/

example : Core.Proves StandardExample .solkey [] .nil
    cdl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 } := by
  sol_prove

example : Core.Proves StandardExample .solkey [] .nil
    cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] true } := by
  sol_prove

/-- The walk under `⊢ₖ`: every step rule's `hR` by `rule_admits`. -/
example : Core.Proves StandardExample .solkey [] .nil
    cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] true } := by
  refine Core.Proves.allRight ?_
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

-- Off the fragment `sol_prove` gives up under `⊢ₖ`: solkey has no rule
-- for a loop (`Core.loopFalse`, `[ while (false) { } ] true`).
/--
error: sol_prove: the walk does not reach the end of the sequent: a step with no rule, a leaf `Proves.close` does not take (`Fml.closableB`: a modality left, a negated or assumed part not first-order, or a hidden binder's name reused), or more than 20000 steps
-/
#guard_msgs in
example : Core.Proves StandardExample .solkey [] .nil (Core.loopFalse (C := StandardExample)) := by
  sol_prove

/-- The calculus derives it (`Core.loopFalse_derived`). -/
example : Core.Proves StandardExample .all [] .nil (Core.loopFalse (C := StandardExample)) := by
  sol_prove

/-! ## Today's short walk

Under `open scoped Solidity.Core.Surface` `sol_derive?` writes today's walk
text, which the scope's macros read (`Calculus/Core/WalkSyntax.lean`):
solkey's aliases, one `apply` per rule, `refine close ?_` at a leaf, the
steps KeY does not show left unwritten.  A `∀` written in the formula is
not a parameter (`cdl!` marks it, decision 28): it gets its `apply
allRight` line. -/

section Surface

open scoped Solidity.Core.Surface

open Proves

/--
info: Try this:
  apply Proves.valid
    apply allRight
    apply unfold .localValueDeclInitDrop
    apply update .binopAssignment
    apply unfold .ifElseUnfold
    apply unfold .localValueDeclInitDrop
    apply update .binopAssignment
    apply splitBox .ifElseSplit
    case thn =>
      apply update .storageRootWriteStore
      refine close ?_
      sol_symex
      sol_close
    case els =>
      apply update .storageRootWriteStore
      refine close ?_
      sol_symex
      sol_close
-/
#guard_msgs in
example : ⊨ dl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] total != 0 } := by
  sol_derive?

/-- The suggestion replayed. -/
example : ⊨ dl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] total != 0 } := by
  apply Proves.valid
  apply allRight
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply unfold .ifElseUnfold
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply splitBox .ifElseSplit
  case thn =>
    apply update .storageRootWriteStore
    refine close ?_
    sol_symex
    sol_close
  case els =>
    apply update .storageRootWriteStore
    refine close ?_
    sol_symex
    sol_close

/--
info: Try this:
  apply impRight
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply unfold .requireConditionCapture
    apply unfold .localValueDeclInitDrop
    apply update .binopAssignment
    apply splitBox .requireSimple
    case thn =>
      refine close ?_
      sol_symex
      sol_close
    case els =>
      apply done .revertBox
      refine close ?_
      sol_symex
      sol_close
-/
#guard_msgs in
example : ⊢ dl!{ a == 1 → [ uint x = a; require(x == 1); ] x == 1 } := by
  sol_derive?

/-- The suggestion replayed. -/
example : ⊢ dl!{ a == 1 → [ uint x = a; require(x == 1); ] x == 1 } := by
  apply impRight
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .requireConditionCapture
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply splitBox .requireSimple
  case thn =>
    refine close ?_
    sol_symex
    sol_close
  case els =>
    apply done .revertBox
    refine close ?_
    sol_symex
    sol_close

/--
info: Try this:
  apply Proves.valid
    apply cases .sendNoCallbackBox <;>
        (try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]) <;>
      (try and_intros)
    · refine close ?_
      sol_symex
      sol_close
    · refine close ?_
      sol_symex
      sol_close
-/
#guard_msgs in
example : ⊨ dl!{ [ ok = to.send(5); ] true } := by
  sol_derive?

/-- The suggestion replayed. -/
example : ⊨ dl!{ [ ok = to.send(5); ] true } := by
  apply Proves.valid
  apply cases .sendNoCallbackBox <;>
      (try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]) <;>
    (try and_intros)
  · refine close ?_
    sol_symex
    sol_close
  · refine close ?_
    sol_symex
    sol_close

end Surface

end Solidity.Examples.Tactics.CoreDerive
