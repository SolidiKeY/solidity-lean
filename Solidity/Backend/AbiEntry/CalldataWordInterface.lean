import Solidity.Semantics.AbiEntry
import Solidity.Source.Eval

/-! Exact zero-padded word access, separate from entry span/length guards.
There is no alignment, canonicality or input-size admission condition. -/
namespace Solidity.Backend.AbiEntry.Interface
structure CalldataWordCertificate : Prop where
  window : ∀ (bytes : List UInt8) (offset width : Nat),
    Solidity.AbiEntry.bytesAt bytes offset width=Source.fitBytes width (bytes.drop offset)
  load : ∀ (frame : Source.Fr) (offset : Nat),
    Solidity.AbiEntry.load frame.cd offset=Source.cdWordAt frame offset
end Solidity.Backend.AbiEntry.Interface
