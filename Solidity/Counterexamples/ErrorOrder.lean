import Solidity.Calculus.RuleSoundness
import Solidity.Semantics.DecEq

/-!
# The value freeze is needed for *error ordering*, not only for interference

`Counterexamples/EvaluationOrder.lean` shows the LHS-unfold residuals writing
the wrong value when the captured path interferes with the value operand.  That
is a *state* disagreement, and it is repaired by `Rules.freezeRhs`.

This file records a second, independent reason the freeze cannot be made
conditional on the path being impure: even when the path **and** the value
operand are pure, the two sides can fail with *different* `Halt`s.

`Semantics.execAssignNested` evaluates the value operand first, so a failing
right-hand side decides the outcome.  An unfrozen target-capture residual
resolves the path first, so a failing path decides it instead.  The two failure
modes are not the same:

* a *simple* right-hand side can only get **stuck** (an unbound variable);
* a pure path can **revert**, because `Semantics.resolveS` runs `evalInt` on
  the index and `Semantics.checkArith` reverts on division by zero.

`people[1 / 0].age = ghost` hits both at once.  It is inside the rule's
condition — the path is complex, the right-hand side is simple and not memory —
and both operands are pure, so no interference argument applies.

This is what the old `hev : rhsToSVal s rhs = .ok (s, sv)` hypothesis was
hiding: assuming the right-hand side *succeeds* removes exactly the states on
which the unfrozen residual is wrong. -/

namespace Solidity
namespace Counterexamples
namespace ErrorOrder

open Rules RuleSoundness Semantics

/-- `people = [default Person]`, and no stack bindings at all — in particular
`ghost` is unbound. -/
def store : State :=
  { State.exampleStore with
      storage :=
        setBy "people" (SVal.array [defaultForRef (RefTy.struct "Person")] [])
          State.exampleStore.storage,
      env := [] }

/-- `people[1 / 0].age = ghost`: a pure path that reverts, and a pure, simple
right-hand side that is stuck. -/
def prog : Stmt := sstmt!{ people[1 / 0].age = ghost }

/-- The rule does apply: complex path, simple non-memory right-hand side. -/
theorem prog_cond :
    (ruleEffect .storageFieldWriteUnfoldLeftFst).cond prog := by
  change _ = true ∧ _ = true ∧ ¬ (_ = true)
  decide

/-- Value operand first: the interpreter is **stuck** on `ghost`. -/
theorem prog_original : execStmt store prog = .error .stuck := by
  native_decide

/-- The residual the rule would emit *without* `Rules.freezeRhs`: capture the
path, then assign. -/
def unfrozenResidual : Block :=
  [ captureStoragePath (sexpr!{ people[1 / 0] }),
    sstmt!{ sp@Person.age = ghost } ]

/-- Path first: the residual **reverts** on `1 / 0`. -/
theorem prog_unfrozen : execBlock store unfrozenResidual = .error .revert := by
  native_decide

/-- **The unfrozen residual is unsound on a pure path and a pure value.**

So the freeze cannot be guarded on `pureExpr path`: purity of both operands is
not enough, because the disagreement is between two *failures*, not between two
written values. -/
theorem unfrozen_not_sound :
    ¬ ResultsAgree aliasNames (execStmt store prog)
        (execBlock store unfrozenResidual) := by
  rw [prog_original, prog_unfrozen]
  intro h
  exact Halt.noConfusion (h : Halt.stuck = Halt.revert)

end ErrorOrder
end Counterexamples
end Solidity
