import Solidity.Backend.MemoryCopies.SourceStoredElements

/-! Populated declared recursive storage graph and primitive fixed-array controls. -/
namespace Solidity.Backend.MemoryCopies.SourceStoredElementsControls
private def nodeDecl : Source.Decl :=
  ⟨.struct,"Node",none,true,.struct "Node"
    (.structMember (.array (.userType ⟨"Node",[]⟩) .none) "children")
    (.cons (.structMember (.elem .bytes) "payload") .nil)⟩
private def rootDecl : Source.Decl :=
  ⟨.stateVar,"root",none,true,.stateVar (.userType ⟨"Node",[]⟩) none none none false "root" .none⟩
private def numbersDecl : Source.Decl :=
  ⟨.stateVar,"numbers",none,true,.stateVar
    (.array (.elem (.int false 256 (by decide))) (.some (.lit (.num (.dec 2 0 0))))) none none none false "numbers" .none⟩
private def E : Source.Env := ⟨[nodeDecl,rootDecl,numbersDecl]⟩
private def name : Source.DeclName := ⟨none,"Node"⟩
private def path : Source.SPath := ⟨⟨none,"root"⟩,[]⟩
private def childrenPath : Source.SPath := path.go (.field 0)
private def firstPath : Source.SPath := childrenPath.go (.index 0)
private def secondPath : Source.SPath := childrenPath.go (.index 1)
private def numbersPath : Source.SPath := ⟨⟨none,"numbers"⟩,[]⟩
private def frame : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def storage : Source.Storage E.layout E.cellTy :=
  (((((((Source.Storage.empty.write childrenPath (.int 2 (by decide))).write
    (firstPath.go (.field 1)) (.int 2 (by decide))).write
    ((firstPath.go (.field 1)).go (.index 0)) (.fixedBytes [17] rfl)).write
    ((firstPath.go (.field 1)).go (.index 1)) (.fixedBytes [23] rfl)).write
    (path.go (.field 1)) (.int 1 (by decide))).write
    ((path.go (.field 1)).go (.index 0)) (.fixedBytes [65] rfl)).write
    (numbersPath.go (.index 0)) (.int 42 (by decide))).write
    (numbersPath.go (.index 1)) (.int 7 (by decide))
private def before : Source.EMState E [.bool] :=
  (.cons (.bool true) .nil,
    {ex := ⟨⟨fun _ => ⟨⟨17,by decide⟩,3,some 9,storage⟩⟩,Source.Transient.empty,[]⟩,
     heap := (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,events := [],
     logs := [(⟨13,by decide⟩,[1,2])],fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩})
private def firstBytes : StoredSourceBytes frame (firstPath.go (.field 1)) before [17,23] := by
  refine ⟨by decide,⟨rfl,rfl,rfl⟩,?_⟩
  intro index
  rcases index with ⟨index,bound⟩
  cases index with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ index => cases index with
    | zero => exact ⟨rfl,rfl,rfl⟩
    | succ index => change index + 2 < 2 at bound; omega
private def rootBytes : StoredSourceBytes frame (path.go (.field 1)) before [65] := by
  refine ⟨by decide,⟨rfl,rfl,rfl⟩,?_⟩
  intro index
  rcases index with ⟨index,bound⟩
  cases index with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ index => change index + 1 < 1 at bound; omega
private def firstFields : SourceStoredFields frame firstPath before 0 (E.layout.fields name) :=
  .cons (.emptyArray (.struct .memory name) ⟨rfl,rfl,rfl⟩)
    (.cons (.bytes firstBytes) (.nil frame firstPath before 2))
private def secondFields : SourceStoredFields frame secondPath before 0 (E.layout.fields name) :=
  .cons (.emptyArray (.struct .memory name) ⟨rfl,rfl,rfl⟩)
    (.cons (.bytes (bytes := []) ⟨by decide,⟨rfl,rfl,rfl⟩,(fun i => Fin.elim0 i)⟩) (.nil frame secondPath before 2))
private def children : SourceStoredElements frame childrenPath before 0 (.struct .memory name) 2 :=
  .cons (.structValue name firstFields)
    (.cons (.structValue name secondFields) (.nil frame childrenPath before 2 (.struct .memory name)))
private def rootFields : SourceStoredFields frame path before 0 (E.layout.fields name) :=
  .cons (.dynamicArray children (by decide) ⟨rfl,rfl,rfl⟩)
    (.cons (.bytes rootBytes) (.nil frame path before 2))
private def numbers : SourceStoredElements frame numbersPath before 0 (.int .u256) 2 :=
  .cons (.primitive (.int 42 (by decide)) rfl ⟨rfl,rfl,rfl⟩)
    (.cons (.primitive (.int 7 (by decide)) rfl ⟨rfl,rfl,rfl⟩) (.nil frame numbersPath before 2 (.int .u256)))
private def observe {τ : Source.STy}
    (result : Source.R (Source.Val E.layout τ) × Source.EMState E [.bool]) : Option (Nat × Nat) :=
  match result.1 with
  | .ok (.memRef _ root) => some (root,result.2.2.heap.next)
  | _ => none
private def byteContent (heap : Source.Heap E.layout) (root : Nat) : Option (List UInt8) :=
  match heap.get root with
  | some ⟨.bytes .memory,.bytes bytes⟩ => some bytes
  | _ => none
private def refRoot {τ : Source.STy} (data : Source.Data E.layout τ) : Option Nat :=
  match data with
  | .val (.memRef _ root) => some root
  | _ => none
private def childRoots (heap : Source.Heap E.layout) : Option (List (Option Nat)) :=
  match heap.get 7 with
  | some ⟨.array .memory (.struct .memory d) none,.array count _ values⟩ =>
      if d = name then some ((List.finRange count).map (fun i => refRoot (values i))) else none
  | _ => none

theorem declared : E.pathTy path = some (.struct .storage name) ∧
    E.layout.fields name = [.array .memory (.struct .memory name) none,.bytes .memory] ∧
    E.pathTy numbersPath = some (.array .storage (.int .u256) (some 2)) := ⟨rfl,rfl,rfl⟩

theorem recursive_certificate :
    ∃ (data : Source.Data E.layout (.struct .memory name)) (loaded : Source.EMState E [.bool]),
      SourceStorageCopyCertificate frame 37 (.struct .memory name) rfl path before loaded
        (allocatedState data loaded) loaded.2.heap.next data ∧ loaded.2.heap.next = 9 := by
  have budget : rootFields.horizon + 1 + 0 = 37 := by decide +kernel
  have count : before.2.heap.next + rootFields.objects = 9 := by decide +kernel
  simpa only [budget,count] using rootFields.structCopy name before (AllocationExtension.refl before) 0

/-- The recursive declaration has two populated children; only their own arrays are empty. -/
theorem recursive_observation :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 38 (.struct .memory name) path).run before) = some (9,10) := by
  obtain ⟨data,loaded,copy,frontier⟩ := recursive_certificate
  rw [copy.execution]
  change some (loaded.2.heap.next,loaded.2.heap.next + 1) = _
  rw [frontier]

theorem recursive_children :
    let after := ((Source.loadElem (E := E) (Γ := [.bool]) frame 38 (.struct .memory name) path).run before).2
    childRoots after.2.heap = some [some 3,some 6] ∧
      byteContent after.2.heap 2 = some [17,23] ∧ byteContent after.2.heap 5 = some [] ∧
      byteContent after.2.heap 8 = some [65] := by decide +kernel

theorem fixed_certificate :
    ∃ (data : Source.Data E.layout (.array .memory (.int .u256) (some 2))) (loaded : Source.EMState E [.bool]),
      SourceStorageCopyCertificate frame 6 (.array .memory (.int .u256) (some 2)) rfl numbersPath before loaded
        (allocatedState data loaded) loaded.2.heap.next data ∧ loaded.2.heap.next = 1 := by
  have budget : numbers.horizon + 1 + 0 = 6 := by decide +kernel
  have count : before.2.heap.next + numbers.objects = 1 := by decide +kernel
  simpa only [budget,count] using numbers.fixedCopy before (AllocationExtension.refl before) 0

theorem fixed_observation :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 7
      (.array .memory (.int .u256) (some 2)) numbersPath).run before) = some (1,2) := by
  obtain ⟨data,loaded,copy,frontier⟩ := fixed_certificate
  rw [copy.execution]
  change some (loaded.2.heap.next,loaded.2.heap.next + 1) = _
  rw [frontier]

private def integer {τ : Source.STy} (data : Source.Data E.layout τ) : Option Int :=
  match data with
  | .val (.int value _) => some value
  | _ => none
private def numbersContent (heap : Source.Heap E.layout) : Option (List (Option Int)) :=
  match heap.get 1 with
  | some ⟨.array .memory (.int type) (some 2),.array count _ values⟩ =>
      if type = .u256 then some ((List.finRange count).map (fun i => integer (values i))) else none
  | _ => none

theorem fixed_contents :
    let after := ((Source.loadElem (E := E) (Γ := [.bool]) frame 7
      (.array .memory (.int .u256) (some 2)) numbersPath).run before).2
    numbersContent after.2.heap = some [some 42,some 7] := by decide +kernel

private def emptyElements : SourceStoredElements frame (firstPath.go (.field 0)) before 0 (.struct .memory name) 0 :=
  .nil frame (firstPath.go (.field 0)) before 0 (.struct .memory name)

theorem empty_closure : SourceStoredDynamicArray emptyElements :=
  storedDynamicArray emptyElements (by decide) ⟨rfl,rfl,rfl⟩

theorem empty_observation :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 3
      (.array .memory (.struct .memory name) none) (firstPath.go (.field 0))).run before) = some (1,2) := by decide +kernel

theorem closure_inhabited : SourceStoredDynamicArray children ∧ SourceStoredFixedArray numbers :=
  ⟨storedDynamicArray children (by decide) ⟨rfl,rfl,rfl⟩,storedFixedArray numbers⟩

theorem old_and_nonheap :
    ∃ data loaded, SourceStorageCopyCertificate frame 37 (.struct .memory name) rfl path before loaded
      (allocatedState data loaded) loaded.2.heap.next data ∧
      (allocatedState data loaded).2.heap.get 0 = before.2.heap.get 0 ∧
      allocatedState data loaded = (before.1,{before.2 with heap := (allocatedState data loaded).2.heap}) := by
  obtain ⟨data,loaded,copy,_⟩ := recursive_certificate
  exact ⟨data,loaded,copy,copy.old 0 (by change 0 < 1; decide),copy.nonheap⟩

theorem alias_rejected :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 38 (.struct .memory name) path).run before) ≠ some (3,4) := by
  rw [recursive_observation]
  decide

theorem horizon_refusal :
    let result := (Source.loadElem (E := E) (Γ := [.bool]) frame 4 (.struct .memory name) path).run before
    result.1 = .error .timeout ∧ result.2 = before := ⟨rfl,rfl⟩

#print axioms declared
#print axioms recursive_certificate
#print axioms recursive_observation
#print axioms recursive_children
#print axioms fixed_certificate
#print axioms fixed_observation
#print axioms fixed_contents
#print axioms empty_closure
#print axioms empty_observation
#print axioms closure_inhabited
#print axioms old_and_nonheap
#print axioms alias_rejected
#print axioms horizon_refusal
end Solidity.Backend.MemoryCopies.SourceStoredElementsControls
