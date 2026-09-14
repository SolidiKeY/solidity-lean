import Solidity.Examples.Common

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 8000000

/-! ## Control-flow derivations

If-then-else on literal conditions (`ifElseTrue`/`ifElseFalse`/`ifElseNegated`)
and `revert()` in both modalities.

Written in the calculus's notation: `⇝[.rule]` is one rewrite step by that
rule, `⇝*` a chain of them.  The rule name is an index of the step
relation, so Lean checks the attribution -- no separate list of rule
names is needed above each derivation. -/

/-! ### `if (true) { age = amount } else { age = i }` -/

/-- `if (true) { … } else { … }` collapses to the then-branch, which is then
a plain root write. -/
sol_derivation ifElseTrueThenWrite :
    solbox!{ if (true) { age = amount } else { age = i } }
  ⇝[.ifElseTrue]               solbox!{ age = amount }
  ⇝[.storageRootWriteStore] solbox!{}

/-! ### `if (false) { age = amount } else { age = i }` -/

sol_derivation ifElseFalseThenWrite :
    solbox!{ if (false) { age = amount } else { age = i } }
  ⇝[.ifElseFalse]              solbox!{ age = i }
  ⇝[.storageRootWriteStore] solbox!{}

/-! ### `if (!true) { age = i } else { age = amount }`
`ifElseNegated` drops the negation by swapping the branches. -/

sol_derivation ifElseNegatedThenWrite :
    solbox!{ if (!true) { age = i } else { age = amount } }
  ⇝[.ifElseNegated]            solbox!{ if (true) { age = amount } else { age = i } }
  ⇝[.ifElseTrue]               solbox!{ age = amount }
  ⇝[.storageRootWriteStore] solbox!{}

/-! ### `revert()` — consumed by the modality rules
Whether the enclosing judgment then holds is decided in the semantic
layer: box vacuously, diamond never. -/

example : solbox!{ revert() } ⇝[.revertBox] solbox!{} := by rule_step

example : soldiamond!{ revert() } ⇝[.revertDiamond] soldiamond!{} := by rule_step

end Solidity.Examples
