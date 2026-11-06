import Solidity.Backend.AbiEntry.Premises.CalldataViews

/-! Additive V2 of the pending V11/G34 structural view premise. A lazy decoder
may validate/materialize additional views after entry. Existing captured keys
must remain stable when the family grows. The V1 declarations are unchanged;
no G34 implementation or runtime/path adequacy is supplied here. -/
namespace Solidity.Backend.AbiEntry.Premises

/-- Extend an already packed prefix, retaining every existing captured key.
The new lookup/raw-reference/input facts come from grown. Only demanded valid
payloads are appended; coherence is still the G40 caller's proof obligation. -/
structure V11G34_ViewExtension {D : Source.Layout} {input : List UInt8}
    {priorViews : List (CalldataView D)} (prior : V11G34_PackedViews input priorViews)
    (additional : List (CalldataView D)) where
  grown : V11G34_PackedViews input (priorViews ++ additional)
  prefix_keys : ∀ (oldIndex : Fin priorViews.length)
    (newIndex : Fin (priorViews ++ additional).length),
    oldIndex.val = newIndex.val → prior.key oldIndex = grown.key newIndex

/-- Required V11/G34 producer shape for lazy-view consumers. Initial packing
is inherited from V1; extension universally preserves the old finite view-key
prefix. No canonical-layout, raw-address disjointness or eager-validation
restriction is introduced. Native access/slice/copy execution is separate. -/
structure V11G34_OverlappingCalldataViewsV2 (D : Source.Layout)
    extends V11G34_OverlappingCalldataViews D where
  extend : (input : List UInt8) → (priorViews additional : List (CalldataView D)) →
    (prior : V11G34_PackedViews input priorViews) →
    V11G34_ViewCoherence (priorViews ++ additional) → V11G34_ViewExtension prior additional

end Solidity.Backend.AbiEntry.Premises
