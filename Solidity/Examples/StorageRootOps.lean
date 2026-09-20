import Solidity.Tactics.Derivation

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

/-! ## Storage root operations

Root-level reads, writes, and local rebinds. All are single-step (terminal). -/

/-! ### Example 6: `amount = alice` — root read
`storageRootReadSelect` -/

example : solbox!{ amount = alice } —→ solbox!{} := by single_step storageRootReadSelect

/-! ### Example 7: `alice = bob` — root write copy
`storageRootWriteCopySource` -/

example : solbox!{ alice = bob } —→ solbox!{} := by single_step storageRootWriteCopySource

/-! ### Example 8: `sp = bob` — local rebind
`storageLocalRootRebind` -/

example : solbox!{ sp = bob } —→ solbox!{} := by single_step storageLocalRootRebind

end Solidity.Examples
