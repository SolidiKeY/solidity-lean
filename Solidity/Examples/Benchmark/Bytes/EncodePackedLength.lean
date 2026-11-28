import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `abi.encodePacked` lengths

Source: <https://raw.githubusercontent.com/ethereum/solidity/v0.8.28/docs/abi-spec.rst>, lines 761–769 (Solidity 0.8.28 documentation,
"Non-standard Packed Mode": `int16(-1), bytes1(0x42), uint16(0x03),
string("Hello, world!")` packs to 18 bytes).
Adaptation: the documented encoding's length (`documented`), and the same
three value types at any arguments (`packedValues`).

Natural specification: each value takes its own width, no padding and no
length field: 2 + 1 + 2 (+ 13) bytes.
Status: `documented`, `packedValues` **proved**.
-/

namespace Solidity.Examples.Benchmark.Bytes.EncodePackedLength

def EncodePackedLength : Contract := contract!{
  ensures \result == 18;
  function documented() public pure returns (uint256) {
    return abi.encodePacked(int16(-1), bytes1(0x42), uint16(0x03), string("Hello, world!")).length;
  }
  ensures \result == 5;
  function packedValues(int16 a, bytes1 b, uint16 c) public pure returns (uint256) {
    return abi.encodePacked(a, b, c).length;
  }
}

local instance : InContract := ⟨EncodePackedLength⟩
open scoped Scoped

/-- The documented example packs to 18 bytes. -/
theorem spec_documented : ⊢ spec!{ documented } := by
  sol_prove
/-- `int16`, `bytes1`, `uint16` pack to 5 bytes at any arguments. -/
theorem spec_packedValues : ⊢ spec!{ packedValues } := by
  sol_prove

end Solidity.Examples.Benchmark.Bytes.EncodePackedLength
