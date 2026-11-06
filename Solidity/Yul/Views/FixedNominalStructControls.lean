import Solidity.Yul.Views.FixedNominalStruct
import Solidity.Yul.Views.FixedNominalMemoryControls

/-! A real declared struct has fixed16x2, nominal fixed16x2 and bool fields.
Whole Source writes/unchanged identity are checked against its allocated heap;
dirty preparation remains distinct from a missing-root Source type error. -/
namespace Solidity.Yul.Views.FixedNominalMember.StructControls
open Solidity.Yul.Views

def scaled : Source.DeclName := ⟨none,"Scaled"⟩
def box : Source.DeclName := ⟨none,"Mixed"⟩
def env : Source.Env := ⟨[
  ⟨.udvt,"Scaled",none,true,.udvt "Scaled" (.fixed true (some ⟨16,2,by decide⟩))⟩,
  ⟨.struct,"Mixed",none,true,.struct "Mixed"
    (.structMember (.elem (.fixed true (some ⟨16,2,by decide⟩))) "fixedValue")
    (.cons (.structMember (.userType ⟨"Scaled",[]⟩) "nominalValue")
      (.cons (.structMember (.elem .bool) "flag") .nil))⟩]⟩
def ty : Source.STy := .struct .memory box

def oldFields : Source.DataList env.layout (env.layout.fields box) :=
  .cons (.val (.fixed (-125) (by decide))) (.cons (.val (.udvt (.fixed (-125) (by decide))))
    (.cons (.val (.bool true)) .nil))
def newFields : Source.DataList env.layout (env.layout.fields box) :=
  .cons (.val (.fixed (-32768) (by decide))) (.cons (.val (.udvt (.fixed 32767 (by decide))))
    (.cons (.val (.bool false)) .nil))
def heap : Source.Heap env.layout := (Source.Heap.empty.alloc ⟨ty,.struct oldFields⟩).1
def placement : Placement heap := ComputedPlacement.build heap (by decide) (by decide)
def oldWords : List Roadmap.Word := [Source.intWord (-125),Source.intWord (-125),1]
def newWords : List Roadmap.Word := [Source.intWord (-32768),32767,0]

theorem old_repr : MemoryFields placement oldFields oldWords := by
  first | solve | simp only
        | exact .cons _ _ (.scalar _ _ rfl) _ _ (.cons _ _ (.scalar _ _ rfl) _ _ (.cons _ _ (.scalar _ _ rfl) _ _ .nil))
theorem new_repr : MemoryFields placement newFields newWords := by
  first | solve | simp only
        | exact .cons _ _ (.scalar _ _ rfl) _ _ (.cons _ _ (.scalar _ _ rfl) _ _ (.cons _ _ (.scalar _ _ rfl) _ _ .nil))

def entry : MixedHeapEntry placement := ⟨0,ty,.struct oldFields,rfl,.words _ _ (.strct oldFields oldWords old_repr)⟩
theorem covered : CoversMixedHeap [entry] := by
  first | solve | simp only [CoversMixedHeap]
        | intro a present
          have bound := ComputedPlacement.occupied_lt heap a present
          change a<1 at bound
          have zero : a=0 := by omega
          subst a
          exact ⟨entry,List.mem_cons_self,rfl⟩
theorem profile : ∀ τ∈env.layout.fields box,Supported env τ := by
  intro τ member
  change τ∈[.fixed Solidity.Yul.Views.Controls.scaled16,.udvt scaled,.bool] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with eq | eq | eq <;> subst τ
  · trivial
  · exact ⟨rfl,trivial⟩
  · exact Or.inl (Or.inl rfl)

def state : Source.EMState env [ty,ty] :=
  (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil),
    {ex:=⟨⟨fun _=>Source.Account.empty _⟩,.empty,[]⟩,heap:=heap,events:=[],logs:=[],fnLocals:=⟨[],.nil⟩})
def changed (residual : ByteView) := wordListView newWords residual (placement.address 0)
def expected := withSourceHeap state (heap.write 0 (.struct newFields) (heap_ty_of_get heap 0 _ (.struct oldFields) rfl))

theorem changed_snapshot (residual : ByteView) :
    (snapshotStruct placement [entry] .memory box (changed residual) (placement.address 0)).map InventoryObject.data=
      some (Source.Data.struct (l:=.memory) newFields) := by
  have decoded := decodeFields_reads placement [entry] covered new_repr profile (changed residual) (placement.address 0)
    (fun i w found=>wordList_read newWords residual _ i w found)
  unfold snapshotStruct
  rw [Option.pmap_some' decoded]
  rfl

theorem changed_source (residual : ByteView) : structState state placement [entry] 0 box (changed residual)=some (.ok (),expected) := by
  unfold structState changed
  rw [decodeFields_reads placement [entry] covered new_repr profile _ _
    (fun i w found=>wordList_read newWords residual _ i w found)]
  rw [Option.map_some,structHeapPut_run state 0 box newFields (by rfl)]
  rfl

theorem unchanged_source (residual : ByteView) :
    structState state placement [entry] 0 box (wordListView oldWords residual (placement.address 0))=some (.ok (),state) := by
  apply struct_unchanged state placement [entry] covered 0 box oldFields rfl oldWords old_repr profile
  intro i w found
  exact wordList_read oldWords residual _ i w found

theorem dirty_rejected : structState state placement [entry] 0 box
    (mstore (fun _=>0) (placement.address 0) 65411)=none := rfl

theorem missing_root_error : structState state placement [entry] 1 box (fun _=>0)=
    some (.error (.stuck "memory write type"),state) := rfl

end Solidity.Yul.Views.FixedNominalMember.StructControls
