import Solidity.Yul.Views.FixedNominalFields
import Solidity.Yul.Views.FixedNominalUnchangedControls

/-! A mixed typed field list contains fixed, declared nominal, bool and an
actual owned memory reference. Concrete decoding constructs the original list;
dirty scalar words and unowned pointers remain preparation failures. -/
namespace Solidity.Yul.Views.FixedNominalMember.Controls
open Solidity.Yul.Views

def fieldTypes : List Source.STy := [.fixed FixedNominalMemory.Controls.f,
  .udvt FixedNominalMemory.Controls.name,.bool,FixedNominalMemory.Controls.ty]
def fields : Source.DataList FixedNominalMemory.Controls.env.layout fieldTypes :=
  .cons (.val (.fixed (-125) (by decide)))
    (.cons (.val (.udvt (.fixed (-32768) (by decide))))
      (.cons (.val (.bool true)) (.cons (.val (.memRef rfl 0)) .nil)))
def words : List Roadmap.Word := [Source.intWord (-125),Source.intWord (-32768),1,
  ownedPointerWord FixedNominalMemory.Controls.placement 0 FixedNominalMemory.Controls.ty rfl]

theorem represented : MemoryFields FixedNominalMemory.Controls.placement fields words := by
  first | solve | simp only
        | exact .cons _ _ (.scalar _ _ rfl) _ _
            (.cons _ _ (.scalar _ _ rfl) _ _ (.cons _ _ (.scalar _ _ rfl) _ _
              (.cons _ _ (.pointer rfl 0 _ rfl rfl) _ _ .nil)))

theorem supported : ∀ τ∈fieldTypes,Supported FixedNominalMemory.Controls.env τ := by
  first | solve | simp only [fieldTypes,List.mem_cons,List.not_mem_nil,or_false]
        | intro τ member
          simp only [fieldTypes,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with eq | eq | eq | eq <;> subst τ
          · trivial
          · exact ⟨rfl,trivial⟩
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr (Or.inr rfl))

theorem actual_decode (residual : ByteView) :
    decodeFields FixedNominalMemory.Controls.placement [FixedNominalInventory.Controls.entry]
      fieldTypes (wordListView words residual 512) 512=some fields := by
  first | solve | simp only
        | apply decodeFields_reads _ _ FixedNominalInventory.UnchangedControls.coverage represented supported
          intro i w found
          exact wordList_read words residual 512 i w found

theorem dirty_field_rejected : decodeFields FixedNominalMemory.Controls.placement
    [FixedNominalInventory.Controls.entry] fieldTypes (mstore (fun _=>0) 512 65411) 512=none := by
  first | solve | rfl
        | solve | decide

theorem old_field_decoder_gap : decodeCanonicalFields FixedNominalMemory.Controls.placement
    [FixedNominalInventory.Controls.entry] fieldTypes (fun _=>0) 512=none := rfl

theorem unowned_pointer_rejected : decode FixedNominalMemory.Controls.placement
    [FixedNominalInventory.Controls.entry] FixedNominalMemory.Controls.ty 999=none := rfl

theorem missing_nominal_rejected : decode FixedNominalMemory.Controls.placement
    [FixedNominalInventory.Controls.entry] (.udvt FixedNominalMemory.Controls.missing) 0=none := rfl

end Solidity.Yul.Views.FixedNominalMember.Controls
