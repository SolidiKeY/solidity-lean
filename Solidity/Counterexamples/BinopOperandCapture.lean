import Solidity.Examples.Common
import Solidity.Semantics

/-!
# Two nonsimple operands share one scratch name

`binopUnfoldLeft` and `binopUnfoldRight` both bind `Rules.valueAliasName`,
which is the single name `pv`.  One of them firing is sound — that is what
`Calculus/RuleSoundness.lean` proves, a rule at a time.  Both firing on the *same*
binary operation is not: the second binding captures the first, and the
operation is computed from the right operand twice.

```
  r = alice.age + bob.age
⇝ uint pv = alice.age; r = pv + bob.age      -- binopUnfoldLeft
⇝ uint pv = bob.age;   r = pv + pv           -- binopUnfoldRight, and `pv`
                                             -- on the left is now bob.age
```

With `alice.age = 10` and `bob.age = 5` the rule table reaches `5 + 5`, so it
proves `r == 10` of a program that computes `15`.  Both are below; the
interpreter disagrees with the second, which is the content of this file.

## Why it is the rule and not the model

KeY does not write these two taclets the way `Calculus/Rules.lean` does.
`lessThanCaptureLhs` (`solidityProgramRules.key`) is

```
  \find(v = nse < se)
  \varcond(\newTypeOf(pv1, nse), \newTypeOf(pv2, nse))
  \replacewith(pv1Type pv1 = se; pv2Type pv2 = nse; v = pv2 < pv1;)
```

Two differences, and each one alone would prevent this:

1. the right operand is a `SimpleExpression`, so KeY's Lhs rule does not fire
   at all while the right side is still nonsimple — the Rhs rule goes first;
2. when it does fire it introduces **two** variables, `pv1` and `pv2`, both
   `\new`, so no instantiation can make them the same program variable.

`Rules.binopUnfoldLeft` writes `lv = nse ⊕ e` with `e` unrestricted and one
scratch name.  Fixing it is a change to the rule table — a second alias name,
a residual that binds both operands in KeY's right-then-left order, and the
`Uniqueness`/`RuleValidation`/`RuleSoundness` rows that go with it — and it
moves a `ruleEffect` arm, which is what the external `SolKey` reader's
correspondence proofs are pinned to (`AGENTS.md`).  So it is its own change,
and this file is the refutation that says why it is needed.

Found by `Examples/Derivations/Solkey/`: `sol_wp` proves the same programs and
cannot see this, because it never reads `Calculus/Rules.lean`.
-/

namespace Solidity
namespace Counterexamples

open Semantics SoliditySyntax StandardExample Rules

set_option maxHeartbeats 8000000

/-- What the program means: `10 + 5 = 15`. -/
theorem binopBothOperands_interpreter :
    (sol!{ < alice.age = 10; bob.age = 5;
             uint r = alice.age + bob.age;
             assert((r == 15)) > (true) }).Holds State.testSuiteStore := by
  native_decide

/-- What the rule table computes: `5 + 5`.  The derivation is ordinary — every
step is a pinned taclet application — and it closes on an assertion the
program falsifies. -/
sol_calculus binopBothOperands_calculus from State.testSuiteStore
  { alice.age = 10;
    bob.age = 5;
    uint r = alice.age + bob.age;
    assert((r == 10)) }

/-- And the two disagree: the interpreter refutes what the rule table proved.
`sol!` is a diamond, so a violated `assert` halts with `.revert` and the
judgment is false. -/
theorem binopBothOperands_disagree :
    ¬ (sol!{ < alice.age = 10; bob.age = 5;
              uint r = alice.age + bob.age;
              assert((r == 10)) > (true) }).Holds State.testSuiteStore := by
  native_decide

end Counterexamples
end Solidity
