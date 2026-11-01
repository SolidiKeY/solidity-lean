import Solidity.Yul.Views.AggregateStorageDeclaration

namespace Solidity.Yul.Views

mutual
theorem AggregateStorageDeclaration.pack_end {E τ b} (d : AggregateStorageDeclaration E τ b) : FixedPackEnd d.pack d.endByte := by
  cases d with
  | ordinary old => exact old.pack_end
  | strct name fields found members => exact alignFixedPack_end _ _ (members.pack_end 0)
  | array child aggregate => exact (StorageDeclaration.uintArray (E := E)).pack_end
theorem AggregateStorageFields.pack_end {E τs b} (d : AggregateStorageFields E τs b) (i : Nat) : FixedPackEnd (d.pack i) d.endByte := by
  cases d with
  | nil => intro p a cursor cs stop success; cases success; rfl
  | cons head tail =>
    have good : FixedPackEnd (checkedAggregatePack head) head.endByte := by
      intro p a cursor cs stop success
      exact head.pack_end _ _ _ _ _ (checkedAggregatePack_success head _ _ _ _ _ success).2
    exact packFixedRow_end Source.Step.field (checkedAggregatePack head) tail.pack head.endByte tail.endByte good tail.pack_end i
end

mutual
theorem AggregateStorageDeclaration.end_slot_translation {E τ b} (d : AggregateStorageDeclaration E τ b) : SlotTranslation d.endByte := by
  cases d with
  | ordinary old => exact old.end_slot_translation
  | strct name fields found members => exact roundSlot_slot_translation.comp (members.end_slot_translation.comp roundSlot_slot_translation)
  | array child aggregate => exact (StorageDeclaration.uintArray (E := E)).end_slot_translation
theorem AggregateStorageFields.end_slot_translation {E τs b} (d : AggregateStorageFields E τs b) : SlotTranslation d.endByte := by
  cases d with
  | nil => intro cursor slots; rfl
  | cons head tail => exact head.end_slot_translation.comp tail.end_slot_translation
end

theorem AggregateStorageDeclaration.aligned_end {E τ b} (d : AggregateStorageDeclaration E τ b)
    (start : Nat) (aligned : start%32=0) : d.endByte start = d.endByte 0+start := by
  have same := d.end_slot_translation 0 (start/32)
  have reconstruct : start/32*32 = start := by omega
  simpa only [Nat.zero_add,reconstruct] using same

/-- A derived in-place footprint in words. A nested dynamic array contributes
one header; its separately hashed children do not inflate this stride. -/
def AggregateStorageDeclaration.stride {E τ b} (d : AggregateStorageDeclaration E τ b) : Nat := roundSlot (d.endByte 0)/32

theorem AggregateStorageDeclaration.stride_bytes {E τ b} (d : AggregateStorageDeclaration E τ b) :
    d.stride*32 = roundSlot (d.endByte 0) := by
  have aligned := (roundSlot_spec (d.endByte 0)).2.2
  unfold AggregateStorageDeclaration.stride
  omega

theorem AggregateStorageDeclaration.pack_within_stride {E τ b} (d : AggregateStorageDeclaration E τ b)
    (p a start cs stop) (aligned : start%32=0) (success : d.pack p a start = .ok (cs,stop)) :
    stop ≤ start+d.stride*32 := by
  rw [d.pack_end _ _ _ _ _ success,d.aligned_end start aligned,d.stride_bytes]
  have bound := (roundSlot_spec (d.endByte 0)).1
  omega

theorem aggregate_array_stride {E τ b} (child : AggregateStorageDeclaration E τ b) (aggregate : τ.isValue=false) :
    (AggregateStorageDeclaration.array child aggregate).stride = 1 := by
  change roundSlot ((StorageDeclaration.uintArray (E := E)).endByte 0)/32=1
  rw [dynamic_header_end]
  rfl

/-- Exact old behavior is retained, including its preparation failures. -/
theorem aggregate_ordinary_pack {E τ b} (d : RecursiveStorageDeclaration E τ b) :
    (AggregateStorageDeclaration.ordinary d).pack = d.pack := rfl

theorem aggregate_ordinary_paths {E τ b} (d : RecursiveStorageDeclaration E τ b) :
    (AggregateStorageDeclaration.ordinary d).paths = d.paths := rfl

theorem aggregate_ordinary_end {E τ b} (d : RecursiveStorageDeclaration E τ b) :
    (AggregateStorageDeclaration.ordinary d).endByte = d.endByte := rfl

/-- Only a typed HEADER is packed for an aggregate array. Its element reference
is not an inline scalar value. This follows the actual owner STy.cell. -/
theorem aggregate_array_cell {E : Source.Env} {τ : Source.STy} {p : Source.SPath}
    (typed : E.pathTy p = some (.array .storage τ none)) : E.cellTy p = .int .u256 := by
  simp only [Source.Env.cellTy,typed,Option.map_some,Source.STy.cell,Option.getD_some]

end Solidity.Yul.Views
