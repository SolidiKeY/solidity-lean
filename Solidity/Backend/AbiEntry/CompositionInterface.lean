import Solidity.Semantics.AbiEntry

/-! Ordered raw entry recursion obligations. These retain actual semantic
Entries, original fuel, head extent and reached allocation cursor. No new
decoder/evaluator, runtime admission or compiled body is supplied. -/
namespace Solidity.Backend.AbiEntry.Interface
open Solidity.AbiEntry

structure EntryCompositionCertificate
    (append : {parameters tail : List Param} → Entries parameters → Entries tail → Entries (parameters ++ tail)) : Prop where
  head_extent : ∀ parameters tail, headsOf (parameters ++ tail) = headsOf parameters + headsOf tail
  ordered : ∀ input fuel parameters tail position allocated,
    enter input fuel (parameters ++ tail) position allocated = (do
      let (entries, reached) ← enter input fuel parameters position allocated
      let (remaining, final) ← enter input fuel tail (position + headsOf parameters) reached
      pure (append entries remaining, final))

end Solidity.Backend.AbiEntry.Interface
