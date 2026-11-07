import Solidity.Backend.MemoryCopies.SourceStoredFields

/-! Actual declared mixed primitive/bytes/string storage struct copying. -/
namespace Solidity.Backend.MemoryCopies.SourceStoredFieldsControls
private def structDecl : Source.Decl :=
  ⟨.struct,"Bundle",none,true,.struct "Bundle"
    (.structMember (.elem (.int false 256 (by decide))) "tag")
    (.cons (.structMember (.elem .bytes) "payload") (.cons (.structMember (.elem .string) "name") .nil))⟩
private def rootDecl : Source.Decl :=
  ⟨.stateVar,"root",none,true,.stateVar (.userType ⟨"Bundle",[]⟩) none none none false "root" .none⟩
private def E : Source.Env := ⟨[structDecl,rootDecl]⟩
private def name : Source.DeclName := ⟨none,"Bundle"⟩
private def path : Source.SPath := ⟨⟨none,"root"⟩,[]⟩
private def frame : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def storage : Source.Storage E.layout E.cellTy :=
  (((((Source.Storage.empty.write (path.go (.field 0)) (.int 42 (by decide))).write
    (path.go (.field 1)) (.int 2 (by decide))).write
    ((path.go (.field 1)).go (.index 0)) (.fixedBytes [17] rfl)).write
    ((path.go (.field 1)).go (.index 1)) (.fixedBytes [23] rfl)).write
    (path.go (.field 2)) (.int 1 (by decide))).write
    ((path.go (.field 2)).go (.index 0)) (.fixedBytes [65] rfl)
private def before : Source.EMState E [.bool] :=
  (.cons (.bool true) .nil,
    {ex := ⟨⟨fun _ => ⟨17,3,some 9,storage⟩⟩,Source.Transient.empty,[]⟩,
     heap := (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,events := [],
     logs := [(⟨13,by decide⟩,[1,2])],fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩})
private def bytesInput : StoredSourceBytes frame (path.go (.field 1)) before [17,23] := by
  refine ⟨by decide,⟨rfl,rfl,rfl⟩,?_⟩
  intro index
  rcases index with ⟨index,bound⟩
  cases index with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ index => cases index with
    | zero => exact ⟨rfl,rfl,rfl⟩
    | succ index => change index + 2 < 2 at bound; omega
private def stringInput : StoredSourceBytes frame (path.go (.field 2)) before [65] := by
  refine ⟨by decide,⟨rfl,rfl,rfl⟩,?_⟩
  intro index
  rcases index with ⟨index,bound⟩
  cases index with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ index => change index + 1 < 1 at bound; omega
private def fields : SourceStoredFields frame path before 0 (E.layout.fields name) :=
  .cons (.primitive (.int 42 (by decide)) rfl ⟨rfl,rfl,rfl⟩)
    (.cons (.bytes bytesInput) (.cons (.string stringInput) (.nil frame path before 3)))
private def observe
    (result : Source.R (Source.Val E.layout (.struct .memory name)) × Source.EMState E [.bool]) : Option (Nat × Nat) :=
  match result.1 with
  | .ok (.memRef _ root) => some (root,result.2.2.heap.next)
  | _ => none

theorem declared : E.pathTy path = some (.struct .storage name) ∧
    E.layout.fields name = [.int .u256,.bytes .memory,.string .memory] := ⟨rfl,rfl⟩

theorem actual_copy :
    ∃ (data : Source.Data E.layout (.struct .memory name)) (loaded : Source.EMState E [.bool]),
      SourceStorageCopyCertificate frame 15 (.struct .memory name) rfl path before loaded
        (allocatedState data loaded) loaded.2.heap.next data ∧ loaded.2.heap.next = 3 := by
  have budget : fields.horizon + 1 + 0 = 15 := by decide +kernel
  have count : before.2.heap.next + fields.objects = 3 := by decide +kernel
  simpa only [budget,count] using fields.structCopy name before (AllocationExtension.refl before) 0

theorem root_observation :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 16 (.struct .memory name) path).run before) = some (3,4) := by
  obtain ⟨data,loaded,copy,frontier⟩ := actual_copy
  rw [copy.execution]
  change some (loaded.2.heap.next,loaded.2.heap.next + 1) = _
  rw [frontier]

theorem actual_fields :
    match ((Source.loadMem (E := E) (Γ := [.bool]) frame 15 (.struct .memory name) path).run before).1 with
    | .ok (.struct values) => values.nth 0 (.int .u256) = .ok (.val (.int 42 (by decide))) ∧
        values.nth 1 (.bytes .memory) = .ok (.val (.memRef rfl 1)) ∧
        values.nth 2 (.string .memory) = .ok (.val (.memRef rfl 2))
    | _ => False := ⟨rfl,rfl,rfl⟩

theorem child_contents :
    let after := ((Source.loadElem (E := E) (Γ := [.bool]) frame 16 (.struct .memory name) path).run before).2
    after.2.heap.get 1 = some ⟨.bytes .memory,Source.Data.bytes [17,23]⟩ ∧
      after.2.heap.get 2 = some ⟨.string .memory,Source.Data.string [65]⟩ := ⟨rfl,rfl⟩

theorem old_and_nonheap :
    ∃ data loaded, SourceStorageCopyCertificate frame 15 (.struct .memory name) rfl path before loaded
      (allocatedState data loaded) loaded.2.heap.next data ∧
      (allocatedState data loaded).2.heap.get 0 = before.2.heap.get 0 ∧
      allocatedState data loaded = (before.1,{before.2 with heap := (allocatedState data loaded).2.heap}) := by
  obtain ⟨data,loaded,copy,_⟩ := actual_copy
  exact ⟨data,loaded,copy,copy.old 0 (by change 0 < 1; decide),copy.nonheap⟩

theorem wrong_root_rejected :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 16 (.struct .memory name) path).run before) ≠ some (1,2) := by
  rw [root_observation]
  decide

theorem horizon_refusal :
    let result := (Source.loadElem (E := E) (Γ := [.bool]) frame 8 (.struct .memory name) path).run before
    result.1 = .error .timeout ∧ result.2 = before := ⟨rfl,rfl⟩

#print axioms declared
#print axioms actual_copy
#print axioms root_observation
#print axioms actual_fields
#print axioms child_contents
#print axioms old_and_nonheap
#print axioms wrong_root_rejected
#print axioms horizon_refusal
end Solidity.Backend.MemoryCopies.SourceStoredFieldsControls
