import Solidity.Yul.Views.StructWordRetained
import Solidity.Yul.Views.StructWordHeapControls

/-! Two actual heterogeneous struct writes retain the original allocation
snapshot. The second changes a boolean after a pointer update; both aliases,
other objects and dirty unowned padding remain observable. -/
namespace Solidity.Yul.Views.StructWordRetained.Controls
open Solidity.Yul.Views.Controls
open StructWordStore.Controls

def current := StructWordHeap.Controls.next
def q := StructWordHeap.Controls.placement
def prior : RetainedAllocation mixedPlacement q :=
  history mixedHeap mixedPlacement mixedPlacement (retainInitial _ _) 3 mixedName mixedFields pointerFields rfl

def finalFields := (pointerFields.setNth 0 (.val (Source.Val.bool (D:=mixedLayout) false))).toOption.getD pointerFields
def words := mixedStructWords.set 2 1408
def post := withSourceHeap current (current.2.heap.write 3 (.struct finalFields) (by rfl))
def finalPlacement := structWrittenPlacement current.2.heap q 3 mixedName pointerFields finalFields rfl
def finalHistory := history current.2.heap mixedPlacement q prior 3 mixedName pointerFields finalFields rfl
def patch := mstore pointerPatch 896 0

theorem encoded : MemoryFields q pointerFields words := by
  first | (simp only;done) | decide | omega | rfl | skip
  have types : current.2.heap.ty=mixedHeap.ty := funext (fun a => Source.Heap.write_ty mixedHeap 3 a _ (by rfl))
  exact (StructWordStore.fields_update fields 2 (Source.Val.memRef (τ:=.bytes .memory) rfl 5) 1408
    (.pointer rfl 5 (.bytes .memory) rfl rfl) rfl).transport q types rfl

theorem supported_current : ∀ a τ d,current.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported mixedEnv τ := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro a τ d actual
  by_cases same : a=3
  · subst a
    change (mixedHeap.write 3 (.struct pointerFields) (by rfl)).get 3=some ⟨τ,d⟩ at actual
    rw [Source.Heap.write_get] at actual
    cases actual
    exact supported
  · change (mixedHeap.write 3 (.struct pointerFields) (by rfl)).get a=some ⟨τ,d⟩ at actual
    rw [Source.Heap.write_other mixedHeap same] at actual
    exact StructWordHeap.Controls.support a τ d actual

theorem current_reads : ∀ e∈generatedHeapEntries q,e.image.Reads pointerPatch (q.address e.id) := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro e _
  exact StructWordHeap.reads mixedHeap mixedPlacement mixedEntries mixed_coverage 3 mixedName
    mixedFields pointerFields mixedStructWords fields rfl ⟨2,by decide⟩ (.memRef rfl 5) 1408
    (.pointer rfl 5 (.bytes .memory) rfl rfl) rfl mixedPhysical mixed_all_reads e

theorem source_and_original_snapshot :
    (Source.writeLoc mixedReadFrame 0 (.mem 3 0) (Source.Val.bool (D:=mixedLayout) false)).run current=(.ok (),post) ∧
    RetainedAllocation mixedPlacement finalPlacement ∧
    encodeMixedHeap finalPlacement (generatedHeapEntries finalPlacement) patch=patch ∧
    enumeratedMemoryWriteback post mixedPlacement finalPlacement finalHistory patch=.ok (some (.ok (),post)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact whole mixedHeap.ty current mixedPlacement q prior StructWordHeap.Controls.source_and_whole.2.1
    supported_current mixedReadFrame 0 3 mixedName pointerFields finalFields words encoded rfl ⟨0,by decide⟩
    (.bool false) 0 (.scalar _ _ rfl) rfl pointerPatch current_reads StructWordHeap.Controls.source_and_whole.2.2.2.2.2

theorem actual_sequence :
    ((do Source.writeLoc mixedReadFrame 0 (.mem 3 2) (Source.Val.memRef (τ:=.bytes .memory) rfl 5)
         Source.writeLoc mixedReadFrame 0 (.mem 3 0) (Source.Val.bool (D:=mixedLayout) false)) : Source.EM mixedEnv _ Unit).run mixedState=
      (.ok (),post) := by rfl

theorem observations :
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bool) 3 0)).run post=(.ok (.bool false),post) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 2)).run post=(.ok (.memRef rfl 5),post) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 3)).run post=(.ok (.memRef rfl 0),post) ∧
    (mload patch 960).val=1408 ∧ (mload patch 992).val=128 ∧ patch 1443=0xa5 ∧
    post.1=mixedState.1 ∧ finalPlacement.free=mixedPlacement.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact ⟨rfl,rfl,rfl,by decide,by decide,by decide,rfl,rfl⟩

theorem lost_second_write_negative : mload pointerPatch 896≠mload patch 896 := by decide

theorem wrong_type_after_prefix :
    (Source.writeLoc mixedReadFrame 0 (.mem 3 0) (uintValueOfWord mixedLayout 0)).run current=
      (.error (.stuck "field type"),current) := rfl
end Solidity.Yul.Views.StructWordRetained.Controls
