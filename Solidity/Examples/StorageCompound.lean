import Solidity.Tactics.Derivation

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 8000000

/-! ## Storage compound updates

Compound updates like `alice.age += 1` desugar to a read–compute–write sequence.
At the syntactic rewriting level, we show the desugared block reducing to empty.
Initialized local declarations are first split into a declaration and an
assignment; each resulting statement is then consumed by its named rule. -/

/-! ### Example 18: Desugared `alice.age += 1`
1. `localValueDeclInitDrop`, `valueDeclSkip`, `storageFieldReadFind`
2. `localValueDeclInitDrop`, `valueDeclSkip`, `localValueAssign`
3. `storageFieldWriteSave` -/

example : solbox!{ uint amount = alice.age; uint i = amount; alice.age = i } —↠ solbox!{} :=
  calc
    solbox!{ uint amount = alice.age; uint i = amount; alice.age = i }
        —→ solbox!{ uint amount; amount = alice.age;
              uint i = amount; alice.age = i } := by single_step localValueDeclInitDrop
    _ —→ solbox!{ amount = alice.age;
              uint i = amount; alice.age = i } := by single_step valueDeclSkip
    _ —→ solbox!{ uint i = amount; alice.age = i } := by single_step storageFieldReadFind
    _ —→ solbox!{ uint i; i = amount; alice.age = i } := by single_step localValueDeclInitDrop
    _ —→ solbox!{ i = amount; alice.age = i } := by single_step valueDeclSkip
    _ —→ solbox!{ alice.age = i } := by single_step localValueAssign
    _ —→ solbox!{} := by single_step storageFieldWriteSave

end Solidity.Examples
