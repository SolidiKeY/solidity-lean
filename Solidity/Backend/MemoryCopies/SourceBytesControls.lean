import Solidity.Backend.MemoryCopies.SourceBytes

/-! Populated declared persistent byte copies from actual static storage cells. -/
namespace Solidity.Backend.MemoryCopies.SourceBytesControls
private def declaration : Source.Decl :=
  ⟨.stateVar,"blob",none,true,.stateVar (.elem .bytes) none none none false "blob" .none⟩
private def E : Source.Env := ⟨[declaration]⟩
private def path : Source.SPath := ⟨⟨none,"blob"⟩,[]⟩
private def frame : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def byte : Source.Val E.layout (.fixedBytes 1 (by decide)) := .fixedBytes [7] rfl
private def fill : Nat → Source.Storage E.layout E.cellTy
  | 0 => .empty
  | count + 1 => (fill count).write (path.go (.index count)) byte
private theorem index_injective : Function.Injective (fun index => path.go (.index index)) := by
  intro left right equality
  have steps : [Source.Step.index left] = [Source.Step.index right] := congrArg Source.SPath.steps equality
  exact Source.Step.index.inj (List.cons.inj steps).1
private theorem index_ne_root (index : Nat) : path.go (.index index) ≠ path := by
  intro equality
  have steps : [Source.Step.index index] = [] := congrArg Source.SPath.steps equality
  cases steps

theorem fill_read (count index : Nat) (bound : index < count) :
    (fill count).read (path.go (.index index)) = some byte := by
  induction count generalizing index with
  | zero => omega
  | succ count previous =>
    by_cases last : index = count
    · subst index
      exact Source.Storage.write_read _ _ _
    · rw [fill,Source.Storage.write_other _ (fun equality => last (index_injective equality))]
      exact previous index (by omega)

private def stored (count : Nat)
    (range : Source.IntTy.u256.lo ≤ (count : Int) ∧ (count : Int) ≤ Source.IntTy.u256.hi) :
    Source.Storage E.layout E.cellTy := (fill count).write path (.int count range)
private def before (count : Nat)
    (range : Source.IntTy.u256.lo ≤ (count : Int) ∧ (count : Int) ≤ Source.IntTy.u256.hi) : Source.EMState E [.bool] :=
  (.cons (.bool true) .nil,
    {ex := ⟨⟨fun _ => ⟨⟨17,by decide⟩,3,some 9,stored count range⟩⟩,
      Source.Transient.empty,[]⟩,
     heap := (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,
     events := [],logs := [(⟨13,by decide⟩,[1,2])],fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩})
private def payload (count : Nat) : List UInt8 := List.replicate count 7
private theorem payload_range (count : Nat)
    (range : Source.IntTy.u256.lo ≤ (count : Int) ∧ (count : Int) ≤ Source.IntTy.u256.hi) :
    Source.IntTy.u256.lo ≤ ((payload count).length : Int) ∧
      ((payload count).length : Int) ≤ Source.IntTy.u256.hi := by
  simpa only [payload,List.length_replicate] using range
private def lengthCell (count : Nat)
    (range : Source.IntTy.u256.lo ≤ (count : Int) ∧ (count : Int) ≤ Source.IntTy.u256.hi) :
    PersistentSourceCell frame path (before count range)
      (Source.Val.int (payload count).length (payload_range count range)) := by
  refine ⟨rfl,rfl,?_⟩
  change (stored count range).read path = _
  rw [stored,Source.Storage.write_read]
  simp only [payload,List.length_replicate,cast_eq]
private def payloadCells (count : Nat)
    (range : Source.IntTy.u256.lo ≤ (count : Int) ∧ (count : Int) ≤ Source.IntTy.u256.hi) :
    SourceByteRange frame path (before count range) 0 (payload count) := by
  intro index
  refine ⟨rfl,rfl,?_⟩
  change (stored count range).read (path.go (.index (0 + index.val))) = _
  rw [Nat.zero_add,stored,Source.Storage.write_other _ (index_ne_root index.val),
    fill_read count index.val (by simpa only [payload,List.length_replicate] using index.isLt)]
  simp only [cast_eq]
  have selected : (payload count)[index] = (7 : UInt8) := by
    change (List.replicate count (7 : UInt8))[index.val]'(by exact index.isLt) = 7
    exact List.getElem_replicate _
  exact congrArg (fun value : UInt8 =>
    some (Source.Val.fixedBytes (D := E.layout) (n := 1) (h := by decide) [value] rfl)) selected.symm
private def copied (count : Nat)
    (range : Source.IntTy.u256.lo ≤ (count : Int) ∧ (count : Int) ≤ Source.IntTy.u256.hi) :
    SourceStorageCopyCertificate frame (count + 2) (.bytes .memory) rfl path
      (before count range) (before count range)
      (allocatedState (Source.Data.bytes (l := .memory) (payload count)) (before count range))
      1 (Source.Data.bytes (payload count)) := by
  simpa only [payload,List.length_replicate,Nat.add_zero] using
    sourceBytesCopy frame path (before count range) (payload count) 0 (payload_range count range)
      (lengthCell count range) (payloadCells count range)
private def observe
    (result : Source.R (Source.Val E.layout (.bytes .memory)) × Source.EMState E [.bool]) : Option (List UInt8) :=
  match result.1 with
  | .ok (.memRef _ root) => match result.2.2.heap.get root with
    | some ⟨_,.bytes bytes⟩ => some bytes
    | _ => none
  | _ => none

theorem declared : E.pathTy path = some (.bytes .storage) := rfl

theorem actual_payload (count : Nat)
    (range : Source.IntTy.u256.lo ≤ (count : Int) ∧ (count : Int) ≤ Source.IntTy.u256.hi) :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame (count + 3) (.bytes .memory) path).run
      (before count range)) = some (payload count) := by
  rw [(copied count range).execution]
  rfl

theorem populated_copy :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 5 (.bytes .memory) path).run
      (before 2 (by decide))) = some [7,7] := actual_payload 2 (by decide)

theorem long_copy :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 67 (.bytes .memory) path).run
      (before 64 (by decide))) = some (List.replicate 64 7) := actual_payload 64 (by decide)

theorem empty_copy :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 3 (.bytes .memory) path).run
      (before 0 (by decide))) = some [] := actual_payload 0 (by decide)

theorem old_and_nonheap :
    let after := allocatedState (Source.Data.bytes (l := .memory) (payload 2)) (before 2 (by decide))
    after.2.heap.get 0 = (before 2 (by decide)).2.heap.get 0 ∧
      after = ((before 2 (by decide)).1,{(before 2 (by decide)).2 with heap := after.2.heap}) :=
  ⟨(copied 2 (by decide)).old 0 (by change 0 < 1; decide),(copied 2 (by decide)).nonheap⟩

theorem wrong_payload_rejected :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 5 (.bytes .memory) path).run
      (before 2 (by decide))) ≠ some [8,7] := by
  rw [populated_copy]
  decide

/-- Insufficient horizon refuses before root allocation; this is a Source
 timeout, not an asserted allocation-size panic or out-of-gas result. -/
theorem horizon_refusal :
    let result := (Source.loadElem (E := E) (Γ := [.bool]) frame 4 (.bytes .memory) path).run (before 2 (by decide))
    result.1 = .error .timeout ∧ result.2 = before 2 (by decide) := ⟨rfl,rfl⟩

#print axioms fill_read
#print axioms declared
#print axioms actual_payload
#print axioms populated_copy
#print axioms long_copy
#print axioms empty_copy
#print axioms old_and_nonheap
#print axioms wrong_payload_rejected
#print axioms horizon_refusal
end Solidity.Backend.MemoryCopies.SourceBytesControls
