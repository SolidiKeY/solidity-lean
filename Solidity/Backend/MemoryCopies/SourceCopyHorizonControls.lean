import Solidity.Backend.MemoryCopies.SourceCopyHorizon
import Solidity.Backend.MemoryCopies.SourceStorageFrames

/-! Populated nested Source copies, long bytes, preserved refusals and partial timeout. -/
namespace Solidity.Backend.MemoryCopies.SourceCopyHorizonControls
private def declaration : Source.Decl :=
  ⟨.stateVar,"matrix",none,true,.stateVar (.array (.array (.elem .bytes) .none) .none)
    none none none false "matrix" .none⟩
private def payloadDecl : Source.Decl :=
  ⟨.stateVar,"payload",none,true,.stateVar (.elem .bytes) none none none false "payload" .none⟩
private def E : Source.Env := ⟨[declaration,payloadDecl]⟩
private def path : Source.SPath := ⟨⟨none,"matrix"⟩,[]⟩
private def payloadPath : Source.SPath := ⟨⟨none,"payload"⟩,[]⟩
private def bytesPath : Source.SPath := (path.go (.index 0)).go (.index 0)
private abbrev T : Source.STy := .array .memory (.array .memory (.bytes .memory) none) none
private def frame : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def storage (populated : Bool) : Source.Storage E.layout E.cellTy :=
  let initial := (Source.Storage.empty.write path (.int 2 (by decide))).write payloadPath (.int 64 (by decide))
  if populated then
    (((initial.write (path.go (.index 0)) (.int 1 (by decide))).write bytesPath (.int 2 (by decide))).write
      (bytesPath.go (.index 0)) (.fixedBytes [17] rfl)).write
      (bytesPath.go (.index 1)) (.fixedBytes [23] rfl)
  else initial
private def before (populated : Bool) : Source.EMState E [.bool] :=
  (.cons (.bool true) .nil,
    {ex := ⟨⟨fun _ => ⟨⟨17,by decide⟩,3,some 9,storage populated⟩⟩,Source.Transient.empty,[]⟩,
     heap := (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,events := [],
     logs := [(⟨13,by decide⟩,[1,2])],fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩})
private def observe {type : Source.STy}
    (result : Source.R (Source.Val E.layout type) × Source.EMState E [.bool]) : Option (Nat × Nat) :=
  match result.1 with
  | .ok (.memRef _ root) => some (root,result.2.2.heap.next)
  | _ => none
private theorem finished_of_observation {type : Source.STy}
    (result : Source.R (Source.Val E.layout type) × Source.EMState E [.bool]) (root next : Nat)
    (observed : observe result = some (root,next)) : result.1 ≠ .error .timeout := by
  intro timed
  have empty : observe result = none := by simp only [observe,timed]
  rw [observed] at empty
  cases empty
private def byteContent (heap : Source.Heap E.layout) (root : Nat) : Option (List UInt8) :=
  match heap.get root with
  | some ⟨.bytes .memory,.bytes bytes⟩ => some bytes
  | _ => none
private def refRoot {type : Source.STy} (data : Source.Data E.layout type) : Option Nat :=
  match data with
  | .val (.memRef _ root) => some root
  | _ => none
private def innerRefs (heap : Source.Heap E.layout) (root : Nat) : Option (List (Option Nat)) :=
  match heap.get root with
  | some ⟨.array .memory (.bytes .memory) none,.array count _ values⟩ =>
      some ((List.finRange count).map (fun index => refRoot (values index)))
  | _ => none

theorem certificate_inhabited : SourceCopyHorizonCertificate E [.bool] frame := sourceCopyHorizons E [.bool] frame

theorem nested_observation :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 16 T path).run (before true)) = some (4,5) := by decide +kernel

theorem nested_horizon (slack : Nat) :
    (Source.loadElem (E := E) (Γ := [.bool]) frame (16 + slack) T path).run (before true) =
      (Source.loadElem frame 16 T path).run (before true) :=
  loadElem_horizon frame 16 slack T path (before true) (finished_of_observation _ 4 5 nested_observation)

theorem nested_payloads :
    let heap := ((Source.loadElem (E := E) (Γ := [.bool]) frame 16 T path).run (before true)).2.2.heap
    byteContent heap 1 = some [17,23] ∧ innerRefs heap 2 = some [some 1] ∧ innerRefs heap 3 = some [] := by decide +kernel

theorem long_observation :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 70 (.bytes .memory) payloadPath).run (before true)) = some (1,2) ∧
      byteContent ((Source.loadElem (E := E) (Γ := [.bool]) frame 70 (.bytes .memory) payloadPath).run (before true)).2.2.heap 1 =
        some (List.replicate 64 0) := by decide +kernel

theorem long_horizon (slack : Nat) :
    (Source.loadElem (E := E) (Γ := [.bool]) frame (70 + slack) (.bytes .memory) payloadPath).run (before true) =
      (Source.loadElem frame 70 (.bytes .memory) payloadPath).run (before true) :=
  loadElem_horizon frame 70 slack (.bytes .memory) payloadPath (before true)
    (finished_of_observation _ 1 2 long_observation.1)

private abbrev M : Source.STy := .mapping (.int .u256) (.bytes .memory)
theorem mapping_refusal :
    (Source.loadMem (E := E) (Γ := [.bool]) frame 1 M path).run (before true) =
      (.error (.stuck "a mapping is not copied"),before true) := rfl

theorem mapping_horizon (slack : Nat) :
    (Source.loadMem (E := E) (Γ := [.bool]) frame (1 + slack) M path).run (before true) =
      (.error (.stuck "a mapping is not copied"),before true) := by
  have finished : ((Source.loadMem (E := E) (Γ := [.bool]) frame 1 M path).run (before true)).1 ≠ .error .timeout := by
    rw [mapping_refusal]
    intro impossible
    cases impossible
  exact (loadMem_horizon frame 1 slack M path (before true) finished).trans mapping_refusal

theorem partial_timeout :
    let result := (Source.loadElem (E := E) (Γ := [.bool]) frame 6 T path).run (before false)
    result.1 = .error .timeout ∧ result.2.2.heap.next = 2 := ⟨rfl,rfl⟩

theorem recovered :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 7 T path).run (before false)) = some (3,4) := by decide +kernel

theorem timeout_is_not_stable :
    (Source.loadElem (E := E) (Γ := [.bool]) frame 6 T path).run (before false) ≠
      (Source.loadElem frame 7 T path).run (before false) := by
  intro equal
  have observation : observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 6 T path).run (before false)) =
      observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 7 T path).run (before false)) := congrArg observe equal
  have timed : observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 6 T path).run (before false)) = none := by decide +kernel
  rw [timed,recovered] at observation
  cases observation

theorem old_and_nonheap :
    let result := (Source.loadElem (E := E) (Γ := [.bool]) frame 6 T path).run (before false)
    result.2.2.heap.get 0 = (before false).2.heap.get 0 ∧
      result.2 = ((before false).1,{(before false).2 with heap := result.2.2.heap}) := by
  have extension : AllocationExtension (before false)
      ((Source.loadElem (E := E) (Γ := [.bool]) frame 6 T path).run (before false)).2 :=
    loadElem_allocates frame 6 T path (before false)
  exact ⟨extension.old 0 (by change 0 < 1; decide),extension.frame⟩

#print axioms certificate_inhabited
#print axioms nested_observation
#print axioms nested_horizon
#print axioms nested_payloads
#print axioms long_observation
#print axioms long_horizon
#print axioms mapping_refusal
#print axioms mapping_horizon
#print axioms partial_timeout
#print axioms recovered
#print axioms timeout_is_not_stable
#print axioms old_and_nonheap
end Solidity.Backend.MemoryCopies.SourceCopyHorizonControls
