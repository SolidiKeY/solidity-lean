import Solidity.Calculus.Close

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
* `split r` — the taclet `r` branches (`ifElseSplit`, `requireSimple`,
  `assertSimple`): goals `thn`, `els`, and `cov` (`Branch.lean`);
* `done r` — the taclet `r` closes the modality (`revertBox` to `true`,
  `revertDiamond` to `false`; `Revert.lean`);
* `empty` — `⟨⟩ φ` (or `[] φ`) is `φ`;
* `close` — leave the calculus: what is left is `⊨ Γ → φ`, for `sol_symex`
  and `sol_close`.

`r` is a constructor of the taclet judgement `Taclet C k m s p`, named as
solkey names the rule; hover it to see its taclet.  Unification matches its
`\find` against the first statement and produces the premise, so after each
`apply` the goal is the next line of the derivation, printed as the sequent
`dl{ Γ ⟹ φ }` (`Notation.lean`).  A rule that does not match is refused by
`apply`.  `Proves.valid` turns a derivation into a proof of `⊨ φ`; it is the
only place soundness is used.
-/

namespace Solidity.Examples

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## Every constructor once

`uint x = a; require(x == 1);` under the diamond, from `a == 1`. -/

/-- `a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1`. -/
theorem guardedCopy : ⊢ dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 } := by
  apply intro
  -- dl{ a = 1 ⟹ ⟨ uint x = a; require(x == 1); ⟩ x = 1 }
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  -- dl{ a = 1, { x := a } ⟹ ⟨ require(x == 1); ⟩ x = 1 }
  apply unfold .requireConditionCapture
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  -- dl{ a = 1, { x := a }, { se1 := x == 1 } ⟹ ⟨ require(se1); ⟩ x = 1 }
  apply split .requireSimple
  case thn =>
    -- dl{ …, se1 = true ⟹ ⟨ ⟩ x = 1 }
    apply empty
    apply close
    sol_symex
    sol_close
  case els =>
    -- dl{ …, se1 = false ⟹ ⟨ revert(); ⟩ x = 1 }
    apply done .revertDiamond
    -- dl{ …, se1 = false ⟹ false }: `a = 1` and `x == 1` false contradict
    apply close
    sol_symex
    sol_close
  case cov =>
    -- dl{ a = 1, { x := a }, { se1 := x == 1 } ⟹ ¬(¬se1 = true ∧ ¬se1 = false) }
    apply close
    sol_symex
    sol_close

/-- A derivation is a proof of validity. -/
example : ⊨ dl!{ a == 1 → ⟨ uint x = a; require(x == 1); ⟩ x == 1 } := guardedCopy.valid

/-! ## Wrong rules are refused

The rule's `\find` must match the statement, and its premise the
constructor.  `storageRootWriteStore` is `gsp = se`, a write to a state
variable, so it does not match a field write.  `localValueAssign` produces
an update, so it is an `update` rule, not an `unfold` one.  `revertDiamond`
is for the diamond only. -/

example : ⊢ dl!{ [ alice.age = 10; revert(); ] true } := by
  fail_if_success apply update .storageRootWriteStore
  fail_if_success apply unfold .localValueAssign
  apply update .storageFieldWriteSave
  fail_if_success apply done .revertDiamond
  apply done .revertBox
  apply close
  sol_symex
  sol_close

/-! ## The judgement is not the strategy

The strategy (`Stmt.step`) sends `alice.account.balance = 10;` to Step 2:
capture the source, alias the receiver, then write through the alias.
Soundness does not need that: `storageFieldWriteSave` asks nothing of the
receiver, and applied directly it writes through the whole path at once. -/

/-- `[ alice.account.balance = 10; ] alice.account.balance == 10`, in one rule. -/
theorem deepFieldWriteShortcut :
    ⊢ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } := by
  apply update .storageFieldWriteSave
  -- dl{ { storage := save(storage, alice.account.balance, 10) } ⟹ [ ] find(storage, alice.account.balance) = 10 }
  apply empty
  apply close
  sol_symex
  sol_close

/-- The strategy takes the long way round. -/
theorem deepFieldWriteStrategy :
    ⊢ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } := by
  apply close
  sol_symex
  sol_close

end Solidity.Examples
