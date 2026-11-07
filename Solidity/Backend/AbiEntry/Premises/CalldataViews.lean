import Solidity.Source.State

/-!
# V11/G34 typed overlapping-calldata-view premise

G34 owns paths, aliases and slices. Its structural producer is published in
`Backend/MemoryOps/CalldataViewPacking.lean`; this interface supplies no
decoder, path or native-execution proof. Only already-validated/demanded views are supplied;
packing never requires eagerly validating all accepted lazy references.
G40 must derive each supplied typed payload from the
actual decoder and prove coherence; this interface does NOT assume that work.
The boundary packs already-decoded views into the EXISTING Calldata carrier.
It does not change Source states, interpret opcodes, copy to memory, introduce
an admission restriction, or provide compiler/runtime correctness.
-/
namespace Solidity.Backend.AbiEntry.Premises

/-- One typed view of the original raw input. Different types may observe the
same raw offset and length. Location evidence retains the existing type. -/
structure CalldataView (D : Source.Layout) where
  type : Source.STy
  location : type.loc? = some .calldata
  rawOffset : Nat
  rawLength : Nat
  contents : Source.Data D type

/-- Equal typed raw references must have equal decoded payloads. Heterogeneous
views at the same address are NOT required to have equal types or contents.
G40 discharges this for its actual decoder results; it is not input admission. -/
structure V11G34_ViewCoherence {D : Source.Layout} (views : List (CalldataView D)) : Prop where
  coherent : ∀ (i j : Fin views.length),
    views[i.val].type = views[j.val].type →
    views[i.val].rawOffset = views[j.val].rawOffset →
    views[i.val].rawLength = views[j.val].rawLength →
    HEq views[i.val].contents views[j.val].contents

/-- Exact structural producer result. Raw source references are retained;
logical table keys may distinguish overlapping heterogeneous views. Equal
typed raw identities retain equal logical keys, including duplicate captures.
This identity condition is not a claim about partially overlapping byte regions.
No claim about Source read execution or emitted target code is hidden here. -/
structure V11G34_PackedViews {D : Source.Layout} (input : List UInt8)
    (views : List (CalldataView D)) where
  calldata : Source.Calldata D
  key : Fin views.length → Nat
  rawReference : (i : Fin views.length) → Source.Val D views[i.val].type
  input_exact : calldata.input = input
  raw_exact : ∀ i, rawReference i =
    .cdRef views[i.val].location views[i.val].rawOffset views[i.val].rawLength
  lookup : ∀ i, calldata.objects (key i) =
    some ⟨views[i.val].type, views[i.val].contents⟩
  aliases : ∀ i j, key i = key j ↔
    views[i.val].type = views[j.val].type ∧
    views[i.val].rawOffset = views[j.val].rawOffset ∧
    views[i.val].rawLength = views[j.val].rawLength

/-- Named V11/G34 structural producer contract, inhabited on master.
Coverage is over EVERY coherent finite view family, including repeated raw
addresses with different element types, without a canonical-layout cutoff.
This is structural view packing only. Native read/path/slice execution and
G35 copies remain separate producer/compiler obligations. -/
structure V11G34_OverlappingCalldataViews (D : Source.Layout) where
  pack : (input : List UInt8) → (views : List (CalldataView D)) →
    V11G34_ViewCoherence views → V11G34_PackedViews input views

end Solidity.Backend.AbiEntry.Premises
