import Solidity.Backend.MemoryCopies.SourceStrings

/-! Separately declared Source strings preserve distinct byte order and state. -/
namespace Solidity.Backend.MemoryCopies.SourceStringsControls
private def declaration : Source.Decl :=
  ⟨.stateVar,"text",none,true,.stateVar (.elem .string) none none none false "text" .none⟩
private def E : Source.Env := ⟨[declaration]⟩
private def path : Source.SPath := ⟨⟨none,"text"⟩,[]⟩
private def frame : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def payload (empty : Bool) : List UInt8 := if empty then [] else [17,23]
private def storage (empty : Bool) : Source.Storage E.layout E.cellTy :=
  if empty then Source.Storage.empty.write path (.int 0 (by decide)) else
    (((Source.Storage.empty.write (path.go (.index 0)) (.fixedBytes [17] rfl)).write
      (path.go (.index 1)) (.fixedBytes [23] rfl)).write path (.int 2 (by decide)))
private def before (empty : Bool) : Source.EMState E [.bool] :=
  (.cons (.bool true) .nil,
    {ex := ⟨⟨fun _ => ⟨17,3,some 9,storage empty⟩⟩,Source.Transient.empty,[]⟩,
     heap := (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,events := [],
     logs := [(⟨13,by decide⟩,[1,2])],fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩})
private theorem range (empty : Bool) : Source.IntTy.u256.lo ≤ ((payload empty).length : Int) ∧
    ((payload empty).length : Int) ≤ Source.IntTy.u256.hi := by
  cases empty <;> decide
private def lengthCell (empty : Bool) : PersistentSourceCell frame path (before empty)
    (Source.Val.int (payload empty).length (range empty)) := by
  cases empty <;> exact ⟨rfl,rfl,rfl⟩
private def cells (empty : Bool) : SourceByteRange frame path (before empty) 0 (payload empty) := by
  cases empty with
  | true => intro index; exact Fin.elim0 index
  | false =>
    intro index
    rcases index with ⟨index,bound⟩
    cases index with
    | zero => exact ⟨rfl,rfl,rfl⟩
    | succ index => cases index with
      | zero => exact ⟨rfl,rfl,rfl⟩
      | succ index => change index + 2 < 2 at bound; omega
private def copied (empty : Bool) :
    SourceStorageCopyCertificate frame ((payload empty).length + 2) (.string .memory) rfl path
      (before empty) (before empty)
      (allocatedState (Source.Data.string (l := .memory) (payload empty)) (before empty))
      1 (Source.Data.string (payload empty)) :=
  sourceStringCopies.copy E [.bool] frame path (before empty) (payload empty) 0
    (range empty) (lengthCell empty) (cells empty)
private def observe
    (result : Source.R (Source.Val E.layout (.string .memory)) × Source.EMState E [.bool]) : Option (List UInt8) :=
  match result.1 with
  | .ok (.memRef _ root) => match result.2.2.heap.get root with
    | some ⟨_,.string bytes⟩ => some bytes
    | _ => none
  | _ => none

theorem declared : E.pathTy path = some (.string .storage) := rfl

theorem actual_payload (empty : Bool) :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame ((payload empty).length + 3) (.string .memory) path).run
      (before empty)) = some (payload empty) := by
  rw [(copied empty).execution]
  cases empty <;> rfl

theorem populated_copy :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 5 (.string .memory) path).run
      (before false)) = some [17,23] := actual_payload false

theorem empty_copy :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 3 (.string .memory) path).run
      (before true)) = some [] := actual_payload true

theorem old_and_nonheap :
    let after := allocatedState (Source.Data.string (l := .memory) (payload false)) (before false)
    after.2.heap.get 0 = (before false).2.heap.get 0 ∧
      after = ((before false).1,{(before false).2 with heap := after.2.heap}) :=
  ⟨(copied false).old 0 (by change 0 < 1; decide),(copied false).nonheap⟩

theorem wrong_order_rejected :
    observe ((Source.loadElem (E := E) (Γ := [.bool]) frame 5 (.string .memory) path).run
      (before false)) ≠ some [23,17] := by
  rw [populated_copy]
  decide

theorem horizon_refusal :
    let result := (Source.loadElem (E := E) (Γ := [.bool]) frame 4 (.string .memory) path).run (before false)
    result.1 = .error .timeout ∧ result.2 = before false := ⟨rfl,rfl⟩

#print axioms declared
#print axioms actual_payload
#print axioms populated_copy
#print axioms empty_copy
#print axioms old_and_nonheap
#print axioms wrong_order_rejected
#print axioms horizon_refusal
end Solidity.Backend.MemoryCopies.SourceStringsControls
