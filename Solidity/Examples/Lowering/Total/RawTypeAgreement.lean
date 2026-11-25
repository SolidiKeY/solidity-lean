import Solidity.Correctness.Lowering.Total.RawTypeAgreement.Leaf

/-! Leaf names under both readers and generated rows at a key. The readers' `String` tests do
not reduce in the kernel, so the reading of a concrete name is a `#guard` and the hypothesis of
the example below it. The bridge over whole types follows in `RawTypeAgreement.lean`. -/
namespace Solidity.Examples.Lowering.Total.RawTypeAgreement
open Solidity.Correctness.Lowering.Total RawTypeAgreement
open ReferenceDecode (rawElem readTy)
open Solidity.Semantics (lookupBy)

def C : Contract := { vars := [] }
-- `bytes4`: a `uint` to `elabTyW`, whose rows spell `bytes4` again.
#guard (elabTyW C (.named "bytes4")).toOption == some (.uint, [("", 32), ("#bytes", 4)])
example {e : Source.Elem} (he : rawElem "bytes4" = some e) : ∃ p ws,
    elabTyW C (.named "bytes4") = .ok (.prim p, ws) ∧ Decode.elemB ws "" p = some e := leaf_elem he rfl
/-- The rows of a `bytes4[]` value below the binder `m`: first lookup and the element type. -/
example : lookupBy "m[]#bytes" (rebase "m" [("[]", 32), ("[]#bytes", 4)]) = some 4 :=
  lookupBy_rebase "m" "[]#bytes" _
example : Decode.elemB (rebase "m[]" [("", 32), ("#bytes", 4)]) "m[]" .uint =
    some (.fixedBytes 4 (by decide)) := (elemB_rebase _ _ _).trans (by decide +kernel)
/-- Rows of other binders around the generated ones are not read; a row at the key is. -/
example : StructRows.Agree (readTy "m" (.ref (.array .uint))) (rebase "m" [("[]", 8)])
    ([("n", 8)] ++ rebase "m" [("[]", 8)] ++ [("mm[]", 16)]) := agree_surround (by decide +kernel)
example : lookupBy "m[]" ([("m[]", 16)] ++ rebase "m" [("[]", 8)]) = some 16 := by decide +kernel

end Solidity.Examples.Lowering.Total.RawTypeAgreement
