import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# Derivations with `apply`

How the examples are proved: a theorem is stated in the calculus, `⊢ φ`, and
its proof is a derivation of the judgement `Γ ⊢ φ` (`Logic.lean`), built one
rule at a time with `apply` — the way PLFA builds a typing derivation
`∅ ⊢ M ⦂ A`.  The constructors of `Proves`:

* `intro` — the precondition moves into the context (`impRight`);
* `update r` — the taclet `r` turns the first statement into an update,
  which moves into the context `Γ`;
* `unfold r` — the taclet `r` replaces the first statement by new ones;
* `split r` — the taclet `r` branches (`ifElseSplit`, `requireSimple`):
  goals `thn` and `els` (`Branch.lean`);
* `check r` — the taclet `r` checks (`assertSimple`): goals `thn`, the rest
  with the condition assumed, and `els`, the condition (`Revert.lean`);
* `done r` — the taclet `r` closes the modality (`revertBox` to `true`,
  `revertDiamond` to `false`; `Revert.lean`);
* `empty` — `⟨⟩ φ` (or `[] φ`) is `φ`;
* `sol_leaf` — leave the calculus once no modality is left: what is left is
  `⊨ Γ → φ`, scoped, for `sol_close` (`Proves.closeValid`, which checks
  that no modality is left).

`sol_derive` runs the strategy as such a derivation: the rule `Stmt.step`
picks at every goal, until only `close` is left.

`r` is a constructor of the taclet judgement `Taclet C k m s p`, named as
solkey names the rule; hover it to see its taclet.  Unification matches its
`\find` against the first statement and produces the premise, so after each
`apply` the goal is the next line of the derivation, printed as the sequent
`dl{ Γ ⟹ φ }` (`Calculus/Notation.lean`).  A rule that does not match, or whose
side conditions do not hold (`nsp` where the part is simple, …), is refused
by `apply`.  `Proves.valid` turns a derivation into a proof of `⊨ φ`; it is the
only place soundness is used.
-/

namespace Solidity.Examples.Tactics.ApplySteps


local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## Wrong rules are refused

The rule's `\find` must match the statement, and its premise the
constructor.  `storageRootWriteStore` is `gsp = se`, a write to a state
variable, so it does not match a field write.  `localValueAssign` produces
an update, so it is an `update` rule, not an `unfold` one.  `revertDiamond`
is for the diamond only, and `empty` for a modality with no statement left. -/

example : ⊢ dl!{ [ alice.age = 10; revert(); ] true } := by
  fail_if_success apply empty
  fail_if_success apply update .storageRootWriteStore
  fail_if_success apply unfold .localValueAssign
  apply update .storageFieldWriteSave
  fail_if_success apply done .revertDiamond
  apply done .revertBox
  sol_leaf
  sol_close

/-! ## The judgement is the strategy

`Stmt.step` sends `alice.account.balance = 10;` to Step 2: capture the
source, alias the receiver, then write through the alias.  That is the only
rule for it (`Rule.premise_unique`): `storageFieldWriteSave` writes through an
`sp`, a simple path, and `alice.account` is not one, so its side condition
refuses the shortcut through the whole path at once. -/

/-- `[ alice.account.balance = 10; ] alice.account.balance == 10`: the
shortcut is refused, and Step 2 is the rule; `sol_derive` then takes the rest
as a derivation. -/
theorem deepFieldWriteStep2 :
    ⊢ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } := by
  fail_if_success apply update .storageFieldWriteSave
  apply unfold .storageFieldWrite_unfold_leftFst
  -- dl{ ⟹ [ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ]
  --       find(storage, alice.account.balance) = 10 }
  sol_derive
  sol_leaf
  sol_close

/-! ## Every constructor once

`uint x = a; require(x == 1);` under the diamond, from `a == 1`. -/

/-- `a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1`. -/
theorem guardedCopy : ⊢ dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 } := by
  apply intro
  -- dl{ ∀ uint a, a = 1 ⟹ ⟨ uint x = a; require(x == 1); ⟩ x = 1 }
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  -- dl{ ∀ uint a, a = 1, { x := a } ⟹ ⟨ require(x == 1); ⟩ x = 1 }
  apply unfold .requireConditionCapture
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  -- dl{ ∀ uint a, a = 1, { x := a }, { se1 := x == 1 } ⟹ ⟨ require(se1); ⟩ x = 1 }
  apply split .requireSimple
  case thn =>
    -- dl{ …, se1 = true ⟹ x = 1 }: no statement left, `empty` does nothing
    apply empty
    sol_leaf
    sol_close
  case els =>
    -- dl{ …, se1 = false ⟹ ⟨ revert(); ⟩ x = 1 }
    apply done .revertDiamond
    -- dl{ …, se1 = false ⟹ false }: `a = 1` and `x == 1` false contradict
    sol_leaf
    sol_close

/-- A derivation is a proof of validity. -/
example : ⊨ dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 } := guardedCopy.valid

end Solidity.Examples.Tactics.ApplySteps
