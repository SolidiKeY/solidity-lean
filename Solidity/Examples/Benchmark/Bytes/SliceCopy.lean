import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: a `bytes` slice copied

Source: <https://raw.githubusercontent.com/ethereum/solidity/v0.8.28/docs/types/reference-types.rst>, lines 599–626 (Solidity 0.8.28
documentation, "Array Slices": `x[start:end]`, implemented for calldata
arrays; a slice out of range reverts) and lines 58–59 (a calldata slice
assigned to storage is copied).  Not OpenZeppelin's `Bytes.slice`, which
clamps its bounds and never reverts.
Adaptation: the slice of a calldata `bytes` copied to storage; `start`
and `end` are spelled `startIndex` and `endIndex` (`end` is a Lean
keyword).

Natural specification: the stored copy has `endIndex - startIndex` bytes
(a slice out of range reverts, so the box needs no `requires`).  The
elementwise clause cannot be written: it names the calldata parameter,
which an obligation cannot (as in `StringEquality`).

Status of `keep`: **unknown**.  `sol_prove` exhausts the default
heartbeat budget after its 16384-step stage (about 5 minutes), so no leaf
is reached.  Missing: a
rule for a calldata slice saved to storage at a symbolic length (its
`.length` read back) instead of the byte-wise copy loop.
-/

namespace Solidity.Examples.Benchmark.Bytes.SliceCopy

def SliceCopy : Contract := contract!{
  bytes stored;
  ensures stored.length == endIndex - startIndex;
  function keep(bytes calldata data, uint256 startIndex, uint256 endIndex) external {
    stored = data[startIndex:endIndex];
  }
}

local instance : InContract := ⟨SliceCopy⟩
open scoped Scoped

/-- Unknown: the length clause of `keep` (see the module docstring). -/
def keepTarget := spec!{ keep }

end Solidity.Examples.Benchmark.Bytes.SliceCopy
