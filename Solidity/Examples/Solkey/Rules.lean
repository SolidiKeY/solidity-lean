import Solidity.Wp.Verifier

/-!
# solkey `keyext.solidity.core/src/test/resources/.../examples/*.key`, ported

The 39 rule-level problems `RulesTest` enumerates, hand-written: they are
`.key` files, so there is nothing for `scripts/solkey-port.mjs` to read.

Only seven of them state a *program* judgment. `u` and `v` are the two
`int` program variables of `commonFields.key`; KeY leaves them
unconstrained and a premise such as `u = 42 ->` supplies their value,
which ports to a declaration.

The other thirty-two are term-level: they assert heap-algebra identities
such as `selectSt(storeSt(mtSt, balance, 10), balance) = 10`
(`simpleExample1.key`) with no program at all, or they exercise the KeY
loader and taclet machinery (`hasSortVarcondTest`, `listTests`,
`schemaVarExample`'s sort conditions, `errors/*`). They are recorded
`unsupported` in `tests/solkey/expected.tsv`: `sol_wp` proves dynamic
logic judgments, and a bare equation between store terms is not one. The
corresponding *rules* are not untested here — they are what
`RuleValidation.lean` and `RuleSoundness.lean` cover.
-/

namespace Solidity
namespace Solkey
namespace Rules

open Semantics Wp

set_option maxHeartbeats 8000000

/-- solkey `assignRuleExample.key`: `u = 42 -> \<{ v = u; }\>(v = 42)`;
the premise on the unconstrained `u` becomes its declaration. -/
theorem solkey_Rules_assignRuleExample :
    (sol!{ < uint u = 42; v = u > (v == 42) }).Holds := by
  sol_wp

/-- solkey `contextAssignTest.key`: two sequential assignments through
context blocks. -/
theorem solkey_Rules_contextAssignTest :
    (sol!{ < v = 42; u = v > (u == 42) }).Holds := by
  sol_wp

/-- solkey `fieldAccessTest.key`: `\<{ value = 42; }\>(true)` — `value`
is the `Token` member of `commonFields.key`, reached here through the
`alice` path the Lean schema gives it. -/
theorem solkey_Rules_fieldAccessTest :
    (sol!{ < alice.account.token.value = 42 > (true) }).Holds := by
  sol_wp

/-- solkey `revert.key`: a plain assignment terminates normally. -/
theorem solkey_Rules_revert :
    (sol!{ < v = 42 > (true) }).Holds := by
  sol_wp

/-- solkey `simpleExpressionTest.key` -/
theorem solkey_Rules_simpleExpressionTest :
    (sol!{ < v = 100 > (v == 100) }).Holds := by
  sol_wp

/-- solkey `schemaVarExample.key`: `\<{ u; }\>(true)` — a bare expression
statement. `u` is declared first because the port starts from a concrete
store, where reading an unbound stack variable is stuck rather than
unconstrained. -/
theorem solkey_Rules_schemaVarExample :
    (sol!{ < uint u = 0; u > (true) }).Holds := by
  sol_wp

/-- solkey `programRulesTest.key`: one `\problem` conjoining four
judgments — the assign rule under a premise, a bare expression statement
under both modalities, and an assignment observed in the postcondition. -/
theorem solkey_Rules_programRulesTest :
    (sol!{ < uint u = 42; v = u > (v == 42) }).Holds
      ∧ (sol!{ < uint u = 0; u > (true) }).Holds
      ∧ (sol!{ [ uint u = 0; u ] (true) }).Holds
      ∧ (sol!{ < v = 42 > (v == 42) }).Holds :=
  ⟨by sol_wp, by sol_wp, by sol_wp, by sol_wp⟩

end Rules
end Solkey
end Solidity
