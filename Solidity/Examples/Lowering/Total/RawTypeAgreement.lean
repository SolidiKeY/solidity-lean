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
/-- A struct name `rawLeaf` writes is the same struct to `elabTyW`, with no rows. -/
example {s : String} {t : Source.Syn .typeName} (ok : ReferenceDecode.rawLeaf C s = .ok t)
    (he : rawElem s = none) : ∃ table, C.structName? s = some table ∧
      elabTyW C (.named s) = .ok (.ref (.struct table), []) :=
  let ⟨table, name, _, _, el⟩ := leaf_struct ok he; ⟨table, name, el⟩
/-- The rows of `mapping(uint8 => uint16[])` at `m`: nested keys, and the key rows `m{}` and
the value rows `m[]…` read apart out of any table that agrees with them. -/
example : rebase "m" ([("[]", 16)].map fun (k, n) => ("[]" ++ k, n)) = rebase "m[]" [("[]", 16)] :=
  rebase_nest "m" "[]" _
example {widths : List (Name × Nat)} (h : StructRows.Agree
    (ReferenceDecode.readRef "m" (.mapping .uint (.ref (.array .uint))))
    (rebase "m" ([("", 8)].map (fun (k, n) => ("{}" ++ k, n)) ++
      [("[]", 16)].map fun (k, n) => ("[]" ++ k, n))) widths) :
    Decode.elemB widths "m{}" .uint = some (.int false 8 (by decide)) ∧
      StructRows.Agree (readTy "m[]" (.ref (.array .uint))) (rebase "m[]" [("[]", 16)]) widths :=
  ⟨(StructRows.elemB_congr (Agree.keyRows h) .uint).symm.trans
    ((elemB_rebase _ _ _).trans (by decide +kernel)), Agree.valueRows h⟩

end Solidity.Examples.Lowering.Total.RawTypeAgreement
