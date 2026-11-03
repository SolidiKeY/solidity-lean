import Solidity.Backend.Aggregates.G18StorageClient

/-! Negative controls over actual declared source paths, populated stores and
NEW transport results. None is external EVM/compiler evidence. -/
namespace Solidity.Backend.Aggregates.StorageClient

/-- Reject wrong output/order/untouched-cell/phase claims; retain the precise
separation between source path typing, allocated target slots and uint8 range.
`isNone = true` identifies the actual Option failure, not an EVM revert. -/
theorem negative_controls :
    (observe sourceAfter targetAfter ≠ [some 8,some 11,some 7,some 11]) ∧ (observe sourceAfter targetAfter ≠ [some 11,some 8,some 11,some 8]) ∧ (observe sourceAfter targetAfter ≠ [some 8,some 8,some 8,some 8]) ∧ (observe sourceAfter target ≠ observe sourceAfter targetAfter) ∧ ((env.pathTy ⟨⟨none,"root"⟩,[.index 0,.field 0]⟩).isNone = true) ∧ (env.pathTy (cell 99) = some (.int .u8)) ∧ ((target.find (selected ⟨99,by decide⟩)).isNone = true) ∧ ((target.save (selected ⟨99,by decide⟩) (.prim (Lowering.V07.integerValue .u8 8 (by decide)))).isNone = true) ∧ (¬(Source.IntTy.u8.lo ≤ (256 : Int) ∧ (256 : Int) ≤ Source.IntTy.u8.hi)) := by
  decide +kernel

/-- info: 'Solidity.Backend.Aggregates.StorageClient.negative_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms negative_controls
end Solidity.Backend.Aggregates.StorageClient
