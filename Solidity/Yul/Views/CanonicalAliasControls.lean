import Solidity.Yul.Views.CanonicalCompatibility
import Solidity.Yul.Views.MemoryScalarControls

namespace Solidity.Yul.Views.Controls

def readCanonAlias (first : Bool) (index : Nat) : Source.EM canonEnv
    [.array .memory canonB3Ty none, .array .memory canonB3Ty none] (Source.Val canonLayout canonB3Ty) := do
  let locals ← Source.EM.locals
  let ref := locals.get (if first then .here else .there .here)
  let loc ← Source.indexLoc mixedReadFrame ref index
  Source.readLoc mixedReadFrame loc

theorem canon_actual_alias_paths :
    (readCanonAlias true 1).run canonRegrowState = (.ok canonB3, canonRegrowState) ∧
    (readCanonAlias false 1).run canonRegrowState = (.ok canonB3, canonRegrowState) := ⟨rfl, rfl⟩

theorem canon_actual_alias_panic : (readCanonAlias false 0).run canonZeroState =
    (.error (.revert (Source.panicData .index)), canonZeroState) := rfl

theorem canonical_bool_all_raw_legacy (word : Roadmap.Word) :
    decodeExtendedMemoryMember boolPlacement [boolEntry] .bool word = decodeMemoryMember boolPlacement [boolEntry] .bool word :=
  decodeExtendedMemoryMember_legacy _ _ .bool (Or.inl rfl) word

theorem canonical_u256_all_raw_legacy (word : Roadmap.Word) :
    decodeExtendedMemoryMember mixedPlacement mixedEntries (.int Source.IntTy.u256) word =
      decodeMemoryMember mixedPlacement mixedEntries (.int Source.IntTy.u256) word :=
  decodeExtendedMemoryMember_legacy _ _ _ (Or.inr (Or.inl rfl)) word

theorem canonical_pointer_all_raw_legacy (word : Roadmap.Word) :
    decodeExtendedMemoryMember mixedPlacement [] (.bytes .memory) word = decodeMemoryMember mixedPlacement [] (.bytes .memory) word :=
  decodeExtendedMemoryMember_legacy _ _ _ (Or.inr (Or.inr rfl)) word

theorem canonical_array_full_result_legacy (m : ByteView) :
    canonicalArrayState boolState boolPlacement [boolEntry] 0 .bool (some 3) 3 boolLength m =
      memberArrayStateWriteback boolState boolPlacement [boolEntry] 0 .bool (some 3) 3 boolLength m :=
  canonicalArrayState_legacy _ _ _ _ _ (Or.inl rfl) _ _ _ _

theorem canonical_retained_beyond_capacity_legacy : canonicalRetainedState retainedRefZeroState mixedPlacement retainedRefZeroPlacement
    retainedRefZeroHistory retainedRefZeroEntries 4 (.bytes .memory) (mstore retainedRefZeroPhysical 1152 3) = none := by
  rw [canonicalRetainedState_legacy _ _ _ _ _ _ _ (Or.inr (Or.inr rfl))]
  unfold retainedMemberArrayState
  rw [show retainedRefZeroPlacement.address 4 = 1152 from rfl, mload_mstore]
  rfl

theorem canonical_dirty_bool_none : decodeExtendedMemoryMember boolPlacement [boolEntry] .bool 2 = none := by
  rw [decodeExtendedMemoryMember_legacy _ _ _ (Or.inl rfl)]
  rfl

def canonAliasChanged (i : Fin 2) : Source.Val canonLayout canonB3Ty := if i.val = 0 then canonB3New else canonB3
def canonAliasChangedWords (i : Fin 2) : Roadmap.Word := if i.val = 0 then canonB3NewWord else canonB3Word
def canonRegrowPlacement := retainedMemberArrayPlacement canonPlacement canonZeroPlacement canonZeroHistory 2 canonB3Ty 0 Fin.elim0 rfl 2 canonBValues (by decide)
def canonAliasChangedHeap := canonRegrowHeap.write 2 (dynamicMemberData canonLayout canonB3Ty 2 canonAliasChanged) (by rfl)
def canonAliasChangedState := withSourceHeap canonRegrowState canonAliasChangedHeap

theorem canon_actual_alias_updated : (readCanonAlias true 0).run canonAliasChangedState = (.ok canonB3New, canonAliasChangedState) ∧
    (readCanonAlias false 0).run canonAliasChangedState = (.ok canonB3New, canonAliasChangedState) ∧
    (readCanonAlias false 1).run canonAliasChangedState = (.ok canonB3, canonAliasChangedState) := ⟨rfl, rfl, rfl⟩

theorem canon_actual_alias_update_MemOK (H : Source.HeapTy) (ok : Source.MemOK canonEnv H canonAliasState) : Source.MemOK canonEnv H canonAliasChangedState := by
  have encoded (i : Fin 2) : MemoryElement canonRegrowPlacement (canonAliasChanged i) (canonAliasChangedWords i) := by
    unfold canonAliasChanged canonAliasChangedWords
    split <;> exact .scalar _ _ (by decide)
  have keep := memberArrayHeapPut_MemOK canonEnv H canonRegrowState canonRegrowPlacement 2 canonB3Ty none 2 (fun _ e => nomatch e)
    canonAliasChanged canonAliasChangedWords encoded (canon_regrow_MemOK H ok)
  rw [memberArrayHeapPut_run canonRegrowState 2 canonB3Ty none 2 (fun _ e => nomatch e) canonAliasChanged (by rfl)] at keep
  exact keep

end Solidity.Yul.Views.Controls
