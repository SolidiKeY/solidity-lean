import Solidity.Backend.MemoryCopies.SourceStoredReferences

/-! Nested declared storage references and an empty dynamically guarded self-reference. -/
namespace Solidity.Backend.MemoryCopies.SourceStoredReferencesControls
private def innerDecl : Source.Decl :=
  ⟨.struct,"Inner",none,true,.struct "Inner"
    (.structMember (.elem .bytes) "payload")
    (.cons (.structMember (.elem .string) "label") .nil)⟩
private def outerDecl : Source.Decl :=
  ⟨.struct,"Outer",none,true,.struct "Outer"
    (.structMember (.userType ⟨"Inner",[]⟩) "first")
    (.cons (.structMember (.userType ⟨"Inner",[]⟩) "second")
      (.cons (.structMember (.array (.elem .bytes) .none) "chunks") .nil))⟩
private def nodeDecl : Source.Decl :=
  ⟨.struct,"Node",none,true,.struct "Node"
    (.structMember (.array (.userType ⟨"Node",[]⟩) .none) "children")
    (.cons (.structMember (.elem .bytes) "payload") .nil)⟩
private def rootDecl : Source.Decl :=
  ⟨.stateVar,"root",none,true,.stateVar (.userType ⟨"Outer",[]⟩) none none none false "root" .none⟩
private def nodeRootDecl : Source.Decl :=
  ⟨.stateVar,"node",none,true,.stateVar (.userType ⟨"Node",[]⟩) none none none false "node" .none⟩
private def E : Source.Env := ⟨[innerDecl,outerDecl,nodeDecl,rootDecl,nodeRootDecl]⟩
private def innerName : Source.DeclName := ⟨none,"Inner"⟩
private def outerName : Source.DeclName := ⟨none,"Outer"⟩
private def nodeName : Source.DeclName := ⟨none,"Node"⟩
private def path : Source.SPath := ⟨⟨none,"root"⟩,[]⟩
private def nodePath : Source.SPath := ⟨⟨none,"node"⟩,[]⟩
private def firstPath : Source.SPath := path.go (.field 0)
private def secondPath : Source.SPath := path.go (.field 1)
private def frame : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def storage : Source.Storage E.layout E.cellTy :=
  (((((Source.Storage.empty.write (firstPath.go (.field 0)) (.int 2 (by decide))).write
    ((firstPath.go (.field 0)).go (.index 0)) (.fixedBytes [17] rfl)).write
    ((firstPath.go (.field 0)).go (.index 1)) (.fixedBytes [23] rfl)).write
    (firstPath.go (.field 1)) (.int 1 (by decide))).write
    ((firstPath.go (.field 1)).go (.index 0)) (.fixedBytes [65] rfl)).write
    (nodePath.go (.field 1)) (.int 0 Source.IntTy.u256.zero_mem)
private def before : Source.EMState E [.bool] :=
  (.cons (.bool true) .nil,
    {ex := ⟨⟨fun _ => ⟨17,3,some 9,storage⟩⟩,Source.Transient.empty,[]⟩,
     heap := (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,events := [],
     logs := [(⟨13,by decide⟩,[1,2])],fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩})
private def bytesInput : StoredSourceBytes frame (firstPath.go (.field 0)) before [17,23] := by
  refine ⟨by decide,⟨rfl,rfl,rfl⟩,?_⟩
  intro index
  rcases index with ⟨index,bound⟩
  cases index with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ index => cases index with
    | zero => exact ⟨rfl,rfl,rfl⟩
    | succ index => change index + 2 < 2 at bound; omega
private def stringInput : StoredSourceBytes frame (firstPath.go (.field 1)) before [65] := by
  refine ⟨by decide,⟨rfl,rfl,rfl⟩,?_⟩
  intro index
  rcases index with ⟨index,bound⟩
  cases index with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ index => change index + 1 < 1 at bound; omega
private def firstFields : SourceStoredFields frame firstPath before 0 (E.layout.fields innerName) :=
  .cons (.bytes bytesInput) (.cons (.string stringInput) (.nil frame firstPath before 2))
private def secondFields : SourceStoredFields frame secondPath before 0 (E.layout.fields innerName) :=
  .cons (.bytes (bytes := []) ⟨by decide,⟨rfl,rfl,rfl⟩,(fun i => Fin.elim0 i)⟩)
    (.cons (.string (bytes := []) ⟨by decide,⟨rfl,rfl,rfl⟩,(fun i => Fin.elim0 i)⟩) (.nil frame secondPath before 2))
private def outerFields : SourceStoredFields frame path before 0 (E.layout.fields outerName) :=
  .cons (.structValue innerName firstFields)
    (.cons (.structValue innerName secondFields)
      (.cons (.byteArray [] (by decide) ⟨rfl,rfl,rfl⟩ (fun i => Fin.elim0 i)) (.nil frame path before 3)))
private def nodeFields : SourceStoredFields frame nodePath before 0 (E.layout.fields nodeName) :=
  .cons (.emptyArray (.struct .memory nodeName) ⟨rfl,rfl,rfl⟩)
    (.cons (.bytes (bytes := []) ⟨by decide,⟨rfl,rfl,rfl⟩,(fun i => Fin.elim0 i)⟩) (.nil frame nodePath before 2))
private def observe {τ : Source.STy}
    (result : Source.R (Source.Val E.layout τ) × Source.EMState E [.bool]) : Option (Nat × Nat) :=
  match result.1 with
  | .ok (.memRef _ root) => some (root,result.2.2.heap.next)
  | _ => none

theorem declared : E.pathTy path = some (.struct .storage outerName) ∧
    E.layout.fields outerName = [.struct .memory innerName,.struct .memory innerName,
      .array .memory (.bytes .memory) none] ∧
    E.layout.fields nodeName = [.array .memory (.struct .memory nodeName) none,.bytes .memory] := ⟨rfl,rfl,rfl⟩

theorem nested_certificate :
    ∃ (data : Source.Data E.layout (.struct .memory outerName)) (loaded : Source.EMState E [.bool]),
      SourceStorageCopyCertificate frame 33 (.struct .memory outerName) rfl path before loaded
        (allocatedState data loaded) loaded.2.heap.next data ∧ loaded.2.heap.next = 8 := by
  have budget : outerFields.horizon + 1 + 0 = 33 := by decide +kernel
  have count : before.2.heap.next + outerFields.objects = 8 := by decide +kernel
  simpa only [budget,count] using outerFields.structCopy outerName before (AllocationExtension.refl before) 0

theorem nested_observation :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 34 (.struct .memory outerName) path).run before) = some (8,9) := by
  obtain ⟨data,loaded,copy,frontier⟩ := nested_certificate
  rw [copy.execution]
  change some (loaded.2.heap.next,loaded.2.heap.next + 1) = _
  rw [frontier]

private def dataRoot {τ : Source.STy} (result : Source.R (Source.Data E.layout τ)) : Option Nat :=
  match result with
  | .ok (.val (.memRef _ root)) => some root
  | _ => none
private def outerRoots (result : Source.R (Source.Data E.layout (.struct .memory outerName))) :
    Option (Option Nat × Option Nat × Option Nat) :=
  match result with
  | .ok (.struct values) => some (dataRoot (values.nth 0 (.struct .memory innerName)),
      dataRoot (values.nth 1 (.struct .memory innerName)),
      dataRoot (values.nth 2 (.array .memory (.bytes .memory) none)))
  | _ => none

theorem actual_fields :
    outerRoots ((Source.loadMem (E := E) (Γ := [.bool]) frame 33 (.struct .memory outerName) path).run before).1 =
      some (some 3,some 6,some 7) := by decide +kernel

private def byteContent (heap : Source.Heap E.layout) (root : Nat) : Option (List UInt8) :=
  match heap.get root with
  | some ⟨.bytes .memory,.bytes bytes⟩ => some bytes
  | _ => none
private def stringContent (heap : Source.Heap E.layout) (root : Nat) : Option (List UInt8) :=
  match heap.get root with
  | some ⟨.string .memory,.string bytes⟩ => some bytes
  | _ => none

theorem nested_contents :
    let after := ((Source.loadElem (E := E) (Γ := [.bool]) frame 34 (.struct .memory outerName) path).run before).2
    byteContent after.2.heap 1 = some [17,23] ∧ stringContent after.2.heap 2 = some [65] ∧
      byteContent after.2.heap 4 = some [] ∧ stringContent after.2.heap 5 = some [] := by decide +kernel

theorem recursive_certificate :
    ∃ (data : Source.Data E.layout (.struct .memory nodeName)) (loaded : Source.EMState E [.bool]),
      SourceStorageCopyCertificate frame 10 (.struct .memory nodeName) rfl nodePath before loaded
        (allocatedState data loaded) loaded.2.heap.next data ∧ loaded.2.heap.next = 3 := by
  have budget : nodeFields.horizon + 1 + 0 = 10 := by decide +kernel
  have count : before.2.heap.next + nodeFields.objects = 3 := by decide +kernel
  simpa only [budget,count] using nodeFields.structCopy nodeName before (AllocationExtension.refl before) 0

/-- Only this empty child array terminates the self-reference; this is not generic graph admission. -/
theorem recursive_observation :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 11 (.struct .memory nodeName) nodePath).run before) = some (3,4) := by
  obtain ⟨data,loaded,copy,frontier⟩ := recursive_certificate
  rw [copy.execution]
  change some (loaded.2.heap.next,loaded.2.heap.next + 1) = _
  rw [frontier]

theorem old_and_nonheap :
    ∃ data loaded, SourceStorageCopyCertificate frame 33 (.struct .memory outerName) rfl path before loaded
      (allocatedState data loaded) loaded.2.heap.next data ∧
      (allocatedState data loaded).2.heap.get 0 = before.2.heap.get 0 ∧
      allocatedState data loaded = (before.1,{before.2 with heap := (allocatedState data loaded).2.heap}) := by
  obtain ⟨data,loaded,copy,_⟩ := nested_certificate
  exact ⟨data,loaded,copy,copy.old 0 (by change 0 < 1; decide),copy.nonheap⟩

theorem alias_rejected :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 34 (.struct .memory outerName) path).run before) ≠ some (3,4) := by
  rw [nested_observation]
  decide

theorem horizon_refusal :
    let result := (Source.loadElem (E := E) (Γ := [.bool]) frame 4 (.struct .memory nodeName) nodePath).run before
    result.1 = .error .timeout ∧ result.2 = before := ⟨rfl,rfl⟩

#print axioms declared
#print axioms nested_certificate
#print axioms nested_observation
#print axioms actual_fields
#print axioms nested_contents
#print axioms recursive_certificate
#print axioms recursive_observation
#print axioms old_and_nonheap
#print axioms alias_rejected
#print axioms horizon_refusal
end Solidity.Backend.MemoryCopies.SourceStoredReferencesControls
