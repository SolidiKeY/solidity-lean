import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: a byte at an index, reverting out of bounds

Source: <https://raw.githubusercontent.com/ethereum/solidity/v0.8.28/docs/types/reference-types.rst>, lines 152–165 ("bytes and string
as Arrays": `bytes` is a `bytes1[]`) and
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.28/docs/control-structures.rst>, line 626 (an index out of bounds fails with
`Panic(0x32)`), Solidity 0.8.28 documentation.  The model reverts there
with no data (`docs/semantic-gaps.md`, "Panic data"); the box accepts the
revert, as solc's `Panic(0x32)` is a revert too (unlike KeY's reading of
`assert`).
Adaptation: one storage `bytes` and its read accessor.

Natural specification: within bounds the result is the stored byte; out of
bounds the call reverts.  Status of `byteAt`: **proved** (`spec_byteAt`,
`byteAt_reverts`).
-/

namespace Solidity.Examples.Benchmark.Bytes.ByteAt

def ByteAt : Contract := contract!{
  bytes data;
  requires i < data.length;
  ensures \result == data[i];
  function byteAt(uint256 i) public view returns (bytes1) {
    return data[i];
  }
}

local instance : InContract := ⟨ByteAt⟩
open scoped Scoped

/-- `byteAt(i)` is `data[i]` within bounds. -/
theorem spec_byteAt : ⊢ spec!{ byteAt } := by
  sol_prove

/-- Out of bounds, `byteAt(i)` reverts: a run of it that terminates
normally had `i < data.length`.  (The same fact stated as
`i >= data.length → [ … ] false` leaves the leaf
`i >= data.length, …, se2 := find(storage, data[se1]) ⟹ false` open: the
closer does not carry the bounds guard to the premise.) -/
theorem byteAt_reverts : ⊨ᶠ dl!{ [ bytes1 r = byteAt(i); ] i < data.length } := by
  sol_symex
  sol_decide

end Solidity.Examples.Benchmark.Bytes.ByteAt
