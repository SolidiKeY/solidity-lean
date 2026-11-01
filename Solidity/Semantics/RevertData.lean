import Solidity.Semantics.Value
import Solidity.RevertBytes

/-!
# Revert data, decoded at a type

`Panic(uint256)`'s code read back as the word `catch Panic(uint c)` binds;
the byte layouts are `RevertBytes.lean`'s.
-/

namespace Solidity.Semantics

/-- The code `catch Panic(uint c)` binds: data that is `Panic`'s selector
and at least one complete word. Trailing bytes are ignored, as pinned solc
`try_decode_panic_data` copies exactly 32 bytes from offset 4. -/
def decodePanic (d : RevertData) : Option Word :=
  if d.take 4 = panicSelector ∧ 36 ≤ d.length then
    let n := bytesNat ((d.drop 4).take 32)
    if h : n < 2 ^ 256 then some ⟨n, by
      simp only [PrimTy.inRange, decide_eq_true_eq]
      exact ⟨Int.natCast_nonneg n, Int.ofNat_lt.mpr h⟩⟩
    else none
  else none

end Solidity.Semantics
