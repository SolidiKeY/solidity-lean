import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `bytes.concat` and `string.concat` lengths

Source: <https://raw.githubusercontent.com/ethereum/solidity/v0.8.28/docs/types/reference-types.rst>, lines 194–208 (Solidity 0.8.28
documentation, "The functions bytes.concat and string.concat").
Changes: none but the spelling of `contract!{ … }`.

Natural specification: the contract's own `assert`s, the length of each
concatenation as the sum of its parts' lengths; `spec!{f}` owes them (an
`assert` is a panic, which the box does not accept).

Status of `f`: **unknown**.  `sol_prove` exhausts the default heartbeat
budget after its 16384-step stage (about 8 minutes): each concatenation is
copied byte by byte over symbolic lengths.  Missing: a length rule for
`concat` (its result's `.length` as the sum of the arguments') instead of
the byte-wise copy loop.
-/

namespace Solidity.Examples.Benchmark.Bytes.ConcatLength

/-- The documentation's contract `C`. -/
def ConcatLength : Contract := contract!{
  string s = "Storage";
  function f(bytes calldata bc, string memory sm, bytes16 b) public view {
    string memory concatString = string.concat(s, string(bc), "Literal", sm);
    assert((bytes(s).length + bc.length + 7 + bytes(sm).length) == bytes(concatString).length);
    bytes memory concatBytes = bytes.concat(bytes(s), bc, bc[:2], "Literal", bytes(sm), b);
    assert((bytes(s).length + bc.length + 2 + 7 + bytes(sm).length + b.length) == concatBytes.length);
  }
}

local instance : InContract := ⟨ConcatLength⟩
open scoped Scoped

/-- Unknown: the two `assert`s of `f` (see the module docstring). -/
def concatTarget := spec!{ f }

end Solidity.Examples.Benchmark.Bytes.ConcatLength
