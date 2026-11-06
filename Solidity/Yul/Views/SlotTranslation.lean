import Solidity.Yul.Views.RecursiveStorageChecked
import Solidity.Yul.Views.RecursiveRootLegacy

namespace Solidity.Yul.Views

/-- Translation by whole physical slots; no wrapping or hash premise is hidden. -/
def SlotTranslation (f : Nat → Nat) : Prop := ∀ cursor slots, f (cursor+slots*32) = f cursor+slots*32

theorem packedStart_slot_translation (cursor width slots : Nat) :
    packedStart (cursor+slots*32) width = packedStart cursor width+slots*32 := by
  have remainder : (cursor+slots*32)%32 = cursor%32 := by omega
  unfold packedStart
  rw [remainder]
  split <;> omega

theorem roundSlot_slot_translation : SlotTranslation roundSlot := by
  intro cursor slots
  unfold roundSlot
  have q : (cursor+slots*32+31)/32 = (cursor+31)/32+slots := by omega
  rw [q,Nat.add_mul]

theorem SlotTranslation.comp {f g : Nat → Nat} (hf : SlotTranslation f) (hg : SlotTranslation g) : SlotTranslation (fun c => g (f c)) := by
  intro cursor slots
  change g (f (cursor+slots*32)) = g (f cursor)+slots*32
  rw [hf cursor slots,hg (f cursor) slots]

theorem fixedElementEnd_slot_translation {f : Nat → Nat} (hf : SlotTranslation f) (n : Nat) : SlotTranslation (fixedElementEnd f n) := by
  induction n with
  | zero => intro cursor slots; rfl
  | succ n ih => exact hf.comp ih

mutual
theorem FixedDeclaration.end_slot_translation {E τ} (d : FixedDeclaration E τ) : SlotTranslation d.endByte := by
  cases d with
  | scalar τ supported =>
    intro cursor slots
    let seed := (declarationScalar? E.layout τ).get supported
    change (seed.position (cursor+slots*32)).start+(seed.position (cursor+slots*32)).field.width =
      (seed.position cursor).start+(seed.position cursor).field.width+slots*32
    rw [seed.position_width,seed.position_width]
    change packedStart (cursor+slots*32) seed.field.width+seed.field.width =
      packedStart cursor seed.field.width+seed.field.width+slots*32
    rw [packedStart_slot_translation]
    omega
  | array n positive child =>
    exact roundSlot_slot_translation.comp ((fixedElementEnd_slot_translation child.end_slot_translation n).comp roundSlot_slot_translation)
  | strct name fields found members => exact roundSlot_slot_translation.comp (members.end_slot_translation.comp roundSlot_slot_translation)
theorem FixedDeclarationFields.end_slot_translation {E τs} (d : FixedDeclarationFields E τs) : SlotTranslation d.endByte := by
  cases d with
  | nil => intro cursor slots; rfl
  | cons head tail => exact head.end_slot_translation.comp tail.end_slot_translation
end

theorem StorageDeclaration.end_slot_translation {E τ} (d : StorageDeclaration E τ) : SlotTranslation d.endByte := by
  cases d with
  | fixed fixed => exact fixed.end_slot_translation
  | uintArray => exact roundSlot_slot_translation.comp ((uintHeaderCell E).end_slot_translation.comp roundSlot_slot_translation)
  | packedUnsignedArray _ _ _ => exact roundSlot_slot_translation.comp ((uintHeaderCell E).end_slot_translation.comp roundSlot_slot_translation)
  | signedArray _ _ => exact roundSlot_slot_translation.comp ((uintHeaderCell E).end_slot_translation.comp roundSlot_slot_translation)
  | scalarArray _ => exact roundSlot_slot_translation.comp ((uintHeaderCell E).end_slot_translation.comp roundSlot_slot_translation)

mutual
theorem RecursiveStorageDeclaration.end_slot_translation {E τ b} (d : RecursiveStorageDeclaration E τ b) : SlotTranslation d.endByte := by
  cases d with
  | leaf old => exact old.end_slot_translation
  | strct name fields found members => exact roundSlot_slot_translation.comp (members.end_slot_translation.comp roundSlot_slot_translation)
theorem RecursiveStorageFields.end_slot_translation {E τs b} (d : RecursiveStorageFields E τs b) : SlotTranslation d.endByte := by
  cases d with
  | nil => intro cursor slots; rfl
  | cons head tail => exact head.end_slot_translation.comp tail.end_slot_translation
end

/-- At an actual aligned start, extent is computed from the same declaration's
zero-based footprint. This is a proved law, not a stride-correctness input. -/
theorem RecursiveStorageDeclaration.aligned_end {E τ b} (d : RecursiveStorageDeclaration E τ b)
    (start : Nat) (aligned : start%32=0) : d.endByte start = d.endByte 0+start := by
  have same := d.end_slot_translation 0 (start/32)
  have reconstruct : start/32*32 = start := by omega
  simpa only [Nat.zero_add,reconstruct] using same

end Solidity.Yul.Views
