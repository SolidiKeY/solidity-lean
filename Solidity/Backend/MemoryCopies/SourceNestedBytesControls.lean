import Solidity.Backend.MemoryCopies.SourceNestedBytes

/-! Declared dynamic bytes arrays with populated children and fresh parents. -/
namespace Solidity.Backend.MemoryCopies.SourceNestedBytesControls
private def declaration : Source.Decl :=
  ⟨.stateVar,"chunks",none,true,.stateVar (.array (.elem .bytes) .none) none none none false "chunks" .none⟩
private def E : Source.Env := ⟨[declaration]⟩
private def path : Source.SPath := ⟨⟨none,"chunks"⟩,[]⟩
private def frame : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private abbrev T : Source.STy := .array .memory (.bytes .memory) none
private def children (populated : Bool) : List (List UInt8) := if populated then [[17,23],[]] else []
private def storage (populated : Bool) : Source.Storage E.layout E.cellTy :=
  if populated then
    ((((Source.Storage.empty.write path (.int 2 (by decide))).write
      (path.go (.index 0)) (.int 2 (by decide))).write
      ((path.go (.index 0)).go (.index 0)) (.fixedBytes [17] rfl)).write
      ((path.go (.index 0)).go (.index 1)) (.fixedBytes [23] rfl))
  else Source.Storage.empty.write path (.int 0 (by decide))
private def state (store : Source.Storage E.layout E.cellTy) : Source.EMState E [.bool] :=
  (.cons (.bool true) .nil,
    {ex := ⟨⟨fun _ => ⟨⟨17,by decide⟩,3,some 9,store⟩⟩,Source.Transient.empty,[]⟩,
     heap := (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,
     events := [],logs := [(⟨13,by decide⟩,[1,2])],fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩})
private def before (populated : Bool) : Source.EMState E [.bool] := state (storage populated)
private theorem range (populated : Bool) : Source.IntTy.u256.lo ≤ ((children populated).length : Int) ∧
    ((children populated).length : Int) ≤ Source.IntTy.u256.hi := by cases populated <;> decide
private def lengthCell (populated : Bool) : PersistentSourceCell frame path (before populated)
    (Source.Val.int (children populated).length (range populated)) := by
  cases populated <;> exact ⟨rfl,rfl,rfl⟩
private def inputs (populated : Bool) : SourceByteChildren frame path (before populated) 0 (children populated) := by
  cases populated with
  | false => intro index; exact Fin.elim0 index
  | true =>
    intro index
    rcases index with ⟨index,bound⟩
    cases index with
    | zero =>
      change StoredSourceBytes frame (path.go (.index 0)) (before true) [17,23]
      refine ⟨by decide,⟨rfl,rfl,rfl⟩,?_⟩
      intro byte
      rcases byte with ⟨byte,bound⟩
      cases byte with
      | zero => exact ⟨rfl,rfl,rfl⟩
      | succ byte => cases byte with
        | zero => exact ⟨rfl,rfl,rfl⟩
        | succ byte => change byte + 2 < 2 at bound; omega
    | succ index => cases index with
      | zero =>
        change StoredSourceBytes frame (path.go (.index 1)) (before true) []
        refine ⟨by decide,⟨rfl,rfl,rfl⟩,?_⟩
        intro byte; exact Fin.elim0 byte
      | succ index => change index + 2 < 2 at bound; omega
private def observe
    (result : Source.R (Source.Val E.layout T) × Source.EMState E [.bool]) : Option (Nat × Nat) :=
  match result.1 with
  | .ok (.memRef _ root) => some (root,result.2.2.heap.next)
  | _ => none

theorem declared : E.pathTy path = some (.array .storage (.bytes .storage) none) := rfl

theorem actual_observation (populated : Bool) :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame
      (byteChildrenHorizon (children populated) + 2) T path).run (before populated)) =
      some (1 + (children populated).length,2 + (children populated).length) := by
  obtain ⟨values,loaded,copy,frontier,_,_⟩ := sourceNestedBytes_copy frame path (before populated)
    (children populated) 0 (range populated) (lengthCell populated) (inputs populated)
  rw [copy.execution]
  change some (loaded.2.heap.next,loaded.2.heap.next + 1) = _
  rw [frontier]
  change some (1 + (children populated).length,1 + (children populated).length + 1) = _
  have next : 1 + (children populated).length + 1 = 2 + (children populated).length := by omega
  rw [next]

theorem populated_copy :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 13 T path).run (before true)) = some (3,4) :=
  actual_observation true

theorem empty_copy :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 3 T path).run (before false)) = some (1,2) :=
  actual_observation false

/-- All child contents survive final parent allocation; their references are
fresh1 and2, while the parent is3. No child read result is assumed. -/
theorem retained_payloads :
    ∃ (values : Fin 2 → Source.Data E.layout (.bytes .memory)) (loaded : Source.EMState E [.bool]),
      let data : Source.Data E.layout T := .array 2 (fun _ impossible => nomatch impossible) values
      SourceStorageCopyCertificate frame 12 T rfl path (before true) loaded
        (allocatedState data loaded) loaded.2.heap.next data ∧ loaded.2.heap.next = 3 ∧
      (allocatedState data loaded).2.heap.get 1 = some ⟨.bytes .memory,Source.Data.bytes [17,23]⟩ ∧
      (allocatedState data loaded).2.heap.get 2 = some ⟨.bytes .memory,Source.Data.bytes []⟩ ∧
      values ⟨0,by decide⟩ = .val (.memRef rfl 1) ∧ values ⟨1,by decide⟩ = .val (.memRef rfl 2) := by
  obtain ⟨values,loaded,copy,frontier,identities,contents⟩ := sourceNestedBytes_copy frame path (before true)
    (children true) 0 (range true) (lengthCell true) (inputs true)
  exact ⟨values,loaded,copy,frontier,contents ⟨0,by decide⟩,contents ⟨1,by decide⟩,
    identities ⟨0,by decide⟩,identities ⟨1,by decide⟩⟩

private def longChildren : List (List UInt8) := List.replicate 64 []
private def longBefore : Source.EMState E [.bool] := state (Source.Storage.empty.write path (.int 64 (by decide)))
private def longInputs : SourceByteChildren frame path longBefore 0 longChildren := by
  intro index
  have empty : longChildren[index] = [] := by
    change (List.replicate 64 ([] : List UInt8))[index.val]'(by exact index.isLt) = []
    exact List.getElem_replicate _
  rw [empty]
  refine ⟨by decide,⟨rfl,rfl,rfl⟩,?_⟩
  intro byte; exact Fin.elim0 byte

theorem long_copy :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 259 T path).run longBefore) = some (65,66) := by
  obtain ⟨values,loaded,copy,frontier,_,_⟩ := sourceNestedBytes_copy frame path longBefore longChildren 0
    (by decide) ⟨rfl,rfl,rfl⟩ longInputs
  have budget : byteChildrenHorizon longChildren + 1 + 0 = 258 := by decide +kernel
  rw [budget] at copy
  rw [copy.execution]
  change some (loaded.2.heap.next,loaded.2.heap.next + 1) = _
  rw [frontier]
  rfl

theorem wrong_root_rejected :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 13 T path).run (before true)) ≠ some (2,3) := by
  rw [populated_copy]
  decide

theorem horizon_refusal :
    let result := (Source.loadElem (E := E) (Γ := [.bool]) frame 7 T path).run (before true)
    result.1 = .error .timeout ∧ result.2 = before true := ⟨rfl,rfl⟩

#print axioms declared
#print axioms actual_observation
#print axioms populated_copy
#print axioms empty_copy
#print axioms retained_payloads
#print axioms long_copy
#print axioms wrong_root_rejected
#print axioms horizon_refusal
end Solidity.Backend.MemoryCopies.SourceNestedBytesControls
