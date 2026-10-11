import Solidity.Calculus.Derive
import Solidity.Calculus.Notation
import Solidity.Calculus.Delab
import Solidity.Calculus.WalkSyntax
import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SolkeyProves

/-!
# The scoped strategy tools

The tactics of `Calculus/Symex.lean` and `Calculus/Derive.lean`
on scoped goals `Valid φ` (`cdl!{ … }`): `sol_symex` then `sol_close`,
`sol_prove` as one kernel evaluation, and `sol_derive?`'s walk, one
`refine` per rule cited by its taclet, each leaf closed (`Proves.close`
and today's closer on its erasure), pinned and replayed; `sol_prove` and
a walk under `⊢ₖ`, solkey's rules alone.
-/

namespace Solidity.Examples.Tactics.Derive

open Solidity

local instance : InContract := ⟨StandardExample⟩

example : Valid cdl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 } := by
  sol_prove

example : Valid cdl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 } := by
  sol_symex
  sol_close

example : Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] total != 0 } := by
  sol_prove

/--
info: Try this:
  refine Proves.valid (R := RuleSet.all) ?_
    refine Proves.allRight ?_
    apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
    apply Proves.update (Taclet.step_eq .binopAssignment)
    apply Proves.unfold (Taclet.step_eq .ifElseUnfold)
    apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
    apply Proves.update (Taclet.step_eq .binopAssignment)
    apply Proves.split (Taclet.step_eq .ifElseSplit)
    case thn =>
      apply Proves.update (Taclet.step_eq .storageRootWriteStore)
      refine Proves.updIntro ?_
      refine Proves.updIntro ?_
      exact Proves.closeTrue rfl
    case els =>
      apply Proves.update (Taclet.step_eq .storageRootWriteStore)
      refine Proves.updIntro ?_
      refine Proves.updIntro ?_
      exact Proves.closeTrue rfl
-/
#guard_msgs in
example : Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] true } := by
  sol_derive?

/-- The suggestion replayed. -/
example : Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] true } := by
  refine Proves.valid (R := RuleSet.all) ?_
  refine Proves.allRight ?_
  apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
  apply Proves.update (Taclet.step_eq .binopAssignment)
  apply Proves.unfold (Taclet.step_eq .ifElseUnfold)
  apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
  apply Proves.update (Taclet.step_eq .binopAssignment)
  apply Proves.split (Taclet.step_eq .ifElseSplit)
  case thn =>
    apply Proves.update (Taclet.step_eq .storageRootWriteStore)
    refine Proves.updIntro ?_
    refine Proves.updIntro ?_
    exact Proves.closeTrue rfl
  case els =>
    apply Proves.update (Taclet.step_eq .storageRootWriteStore)
    refine Proves.updIntro ?_
    refine Proves.updIntro ?_
    exact Proves.closeTrue rfl

example : Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] true } := by
  sol_derive

/-! A leaf with a formula left closes as today's does: `Proves.close` on its
erasure, then `sol_symex; sol_close`. -/

/--
info: Try this:
  refine Proves.valid (R := RuleSet.all) ?_
    refine Proves.allRight ?_
    apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
    apply Proves.update (Taclet.step_eq .binopAssignment)
    apply Proves.unfold (Taclet.step_eq .ifElseUnfold)
    apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
    apply Proves.update (Taclet.step_eq .binopAssignment)
    apply Proves.split (Taclet.step_eq .ifElseSplit)
    case thn =>
      apply Proves.update (Taclet.step_eq .storageRootWriteStore)
      refine Proves.updIntro ?_
      refine Proves.updIntro ?_
      refine Proves.close [] rfl List.nodup_nil ?_
      sol_symex
      sol_close
    case els =>
      apply Proves.update (Taclet.step_eq .storageRootWriteStore)
      refine Proves.updIntro ?_
      refine Proves.updIntro ?_
      refine Proves.close [] rfl List.nodup_nil ?_
      sol_symex
      sol_close
-/
#guard_msgs in
example : Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] total != 0 } := by
  sol_derive?

/-- The suggestion replayed. -/
example : Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] total != 0 } := by
  refine Proves.valid (R := RuleSet.all) ?_
  refine Proves.allRight ?_
  apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
  apply Proves.update (Taclet.step_eq .binopAssignment)
  apply Proves.unfold (Taclet.step_eq .ifElseUnfold)
  apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
  apply Proves.update (Taclet.step_eq .binopAssignment)
  apply Proves.split (Taclet.step_eq .ifElseSplit)
  case thn =>
    apply Proves.update (Taclet.step_eq .storageRootWriteStore)
    refine Proves.updIntro ?_
    refine Proves.updIntro ?_
    refine Proves.close [] rfl List.nodup_nil ?_
    sol_symex
    sol_close
  case els =>
    apply Proves.update (Taclet.step_eq .storageRootWriteStore)
    refine Proves.updIntro ?_
    refine Proves.updIntro ?_
    refine Proves.close [] rfl List.nodup_nil ?_
    sol_symex
    sol_close

/-- `sol_derive` leaves the leaves, as today's does. -/
example : Valid cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] total != 0 } := by
  sol_derive
  all_goals
    refine Proves.close [] rfl List.nodup_nil ?_
    sol_symex
    sol_close

/-! ## solkey's rules alone (`⊢ₖ`)

On `Proves C .solkey …` the walk steps with `Stmt.stepIn .solkey`
(`Calculus/ProvesDerive.lean`): on the fragment it fires solkey's
taclets, and each step rule's `hR` is proved by `rule_admits`
(`Stmt.keyStep` by `rfl`). -/

example : Proves StandardExample .solkey [] .nil
    cdl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 } := by
  sol_prove

example : Proves StandardExample .solkey [] .nil
    cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] true } := by
  sol_prove

/-- The walk under `⊢ₖ`: every step rule's `hR` by `rule_admits`. -/
example : Proves StandardExample .solkey [] .nil
    cdl!{ ∀ uint a; [ uint x = a + 1; if (x > 3) { total = 1; } else { total = 2; }; ] true } := by
  refine Proves.allRight ?_
  apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
  apply Proves.update (Taclet.step_eq .binopAssignment)
  apply Proves.unfold (Taclet.step_eq .ifElseUnfold)
  apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
  apply Proves.update (Taclet.step_eq .binopAssignment)
  apply Proves.split (Taclet.step_eq .ifElseSplit)
  case thn =>
    apply Proves.update (Taclet.step_eq .storageRootWriteStore)
    refine Proves.updIntro ?_
    refine Proves.updIntro ?_
    exact Proves.closeTrue rfl
  case els =>
    apply Proves.update (Taclet.step_eq .storageRootWriteStore)
    refine Proves.updIntro ?_
    refine Proves.updIntro ?_
    exact Proves.closeTrue rfl

-- Off the fragment `sol_prove` gives up under `⊢ₖ`: solkey has no rule
-- for a loop (`loopFalse`, `[ while (false) { } ] true`).
/--
error: sol_prove: the walk does not reach the end of the sequent: a step with no rule, a leaf `Proves.close` does not take (`Fml.closableB`: a modality left, a negated or assumed part not first-order, or a hidden binder's name reused), or more than 20000 steps
-/
#guard_msgs in
example : Proves StandardExample .solkey [] .nil (loopFalse (C := StandardExample)) := by
  sol_prove

/-- The calculus derives it (`loopFalse_derived`). -/
example : Proves StandardExample .all [] .nil (loopFalse (C := StandardExample)) := by
  sol_prove

/-! ## Today's short walk

Under `open scoped Solidity.Scoped` `sol_derive?` writes today's walk
text, which the scope's macros read (`Calculus/WalkSyntax.lean`):
solkey's aliases, one `apply` per rule, `refine close ?_` at a leaf, the
steps KeY does not show left unwritten.  A `∀` written in the formula is
not a parameter (`cdl!` marks it, decision 28): it gets its `apply
allRight` line. -/

section Surface

open scoped Scoped


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

end Solidity.Examples.Tactics.Derive
