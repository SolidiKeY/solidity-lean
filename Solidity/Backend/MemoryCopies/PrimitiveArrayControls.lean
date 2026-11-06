import Solidity.Backend.MemoryCopies.PrimitiveArray
import Solidity.Backend.MemoryCopies.InterfaceV2Laws
import Solidity.Evm.MemoryObjectArrayExamples

/-! Empty, populated and long resolved primitive copies on an actual represented
old heap. Boundary-room refusal is not claimed as runtime panic semantics. -/
namespace Solidity.Backend.MemoryCopies.PrimitiveArrayControls
open Evm Evm.Memory
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,ObjectArrayExamples.initial_allocator⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private def words (payloads : List (Fin W)) : List Word := payloads.map Word.val

private theorem representation (payloads : List (Fin W)) : PrimitiveWords .uint (values payloads) (words payloads) := by
  refine ⟨by simp only [words,values,List.length_map],?_⟩
  intro index value selected
  induction payloads generalizing index with
  | nil => cases selected
  | cons payload payloads ih =>
    cases index with
    | zero => cases selected; exact ⟨.val payload,rfl,ReprV.uint_of rfl⟩
    | succ index => exact ih index selected

private def witness (payloads : List (Fin W)) (fits : 40 + (payloads.length + 1) < W) :
    V2.AllocatorWitness ((values payloads).length + 1) :=
  ⟨input.H,input.heap,input.base,8,wmod 40,input.machine,input.allocator,
    by simpa only [values,List.length_map] using fits⟩
private def chosen (payloads : List (Fin W)) (bounded : payloads.length < W)
    (fits : 40 + (payloads.length + 1) < W) :
    PrimitiveArrayWordCopy .uint (values payloads) (by simpa only [values,List.length_map] using bounded) (words payloads) :=
  primitiveArrayWordCopy .uint (values payloads) _ (words payloads) (representation payloads) (witness payloads fits)
private def grown (payloads : List (Fin W)) (bounded : payloads.length < W) :=
  (primitiveArrayValue .uint (values payloads) (by simpa only [values,List.length_map] using bounded)).copyStToM input.heap rfl
private def observe : Evm.Out → Option (Nat × Nat × Nat × Nat × Nat × Nat)
  | .ok target _ => match target.stack,target.mem 0 with
    | .val root :: _,.val cursor => match target.mem root.val,target.mem (root.val + 1),target.mem (root.val + 2),target.mem 17 with
      | .val length,.val first,.val second,.val old => some (root.val,cursor.val,length.val,first.val,second.val,old.val)
      | _,_,_,_ => none
    | _,_ => none
  | _ => none

/-- The certificate family has an actual represented input for every fitting list. -/
theorem inhabited (payloads : List (Fin W)) (bounded : payloads.length < W)
    (fits : 40 + (payloads.length + 1) < W) :
    Nonempty (PrimitiveArrayWordCopy .uint (values payloads)
      (by simpa only [values,List.length_map] using bounded) (words payloads)) := ⟨chosen payloads bounded fits⟩

theorem empty_copy : observe (run (primitiveArrayCode []) input.machine) = some (40,41,0,0,0,7) := by decide +kernel

theorem pair_copy : observe (run (primitiveArrayCode [w[11],w[23]]) input.machine) = some (40,43,2,11,23,7) := by decide +kernel

private def long : List (Fin W) := (List.range 64).map (fun n => wmod (n + 1))

theorem long_inhabited : Nonempty (PrimitiveArrayWordCopy .uint (values long) (by decide +kernel) (words long)) :=
  inhabited long (by decide +kernel) (by decide +kernel)

theorem actual_length (payloads : List (Fin W)) (bounded : payloads.length < W) :
    (grown payloads bounded).heap.len (grown payloads bounded).val .dyn = payloads.length := by
  dsimp only [grown]
  rw [primitive_array_source]
  simp only [Grown.alloc,Heap.len,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,
    List.length_map,values]

theorem actual_contents (payloads : List (Fin W)) (bounded : payloads.length < W)
    (fits : 40 + (payloads.length + 1) < W) :
    MVal.copyMToSt (grown payloads bounded).heap (grown payloads bounded).val =
      (primitiveArrayValue .uint (values payloads) (by simpa only [values,List.length_map] using bounded)).strip :=
  (chosen payloads bounded fits).certificate.heap.contents input.heap

theorem actual_target (payloads : List (Fin W)) (bounded : payloads.length < W)
    (fits : 40 + (payloads.length + 1) < W) :
    ∃ target : Machine, run (primitiveArrayCode (words payloads)) input.machine = .ok (target.push w[40]) 0 ∧
      target.mem 0 = .val (wmod (40 + payloads.length + 1)) ∧
      target.mem 40 = .val (wmod payloads.length) ∧ target.mem 17 = w[7] ∧ target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (41 + index) = .val payload) := by
  let size : Fin W := ⟨payloads.length,bounded⟩
  let target := arrayWordsMachine (wmod 40) 1 (words payloads) (allocateMachine input.machine (wmod 40) size)
  have wordBound : (words payloads).length < W := by simpa only [words,List.length_map] using bounded
  have same : (⟨(words payloads).length,wordBound⟩ : Fin W) = size := Fin.ext (List.length_map _)
  have ran : run (primitiveArrayCode (words payloads)) input.machine =
      .ok ((arrayWordsMachine (wmod 40) 1 (words payloads)
        (allocateMachine input.machine (wmod 40) ⟨(words payloads).length,wordBound⟩)).push (.val (wmod 40))) 0 :=
    primitive_array_run (words payloads) input.machine (wmod 40) wordBound input.allocator.free.cell
    (by simpa only [words,List.length_map,Nat.add_assoc] using fits)
  rw [same] at ran
  refine ⟨target,ran,?_,?_,?_,?_,?_⟩
  · rw [array_words_other (wmod 40) 1 (words payloads) _ 0 (Or.inl (by decide))]
    rfl
  · rw [array_words_other (wmod 40) 1 (words payloads) _ 40 (Or.inl (by decide))]
    exact (allocateMachine_header input.machine (wmod 40) size (by decide)).trans (congrArg Word.val (Fin.ext (Nat.mod_eq_of_lt bounded).symm))
  · rw [array_words_other (wmod 40) 1 (words payloads) _ 17 (Or.inl (by decide)),
      allocateMachine_other input.machine (wmod 40) size 17 (by decide) (by decide)]
    rfl
  · dsimp only [target]
    rw [array_words_shape]
    rfl
  · intro index payload selected
    have chosen : (words payloads)[index]? = some (.val payload) := by
      simp only [words,List.getElem?_map,selected,Option.map_some]
    exact array_words_selected (wmod 40) 1 (words payloads) _ index (.val payload) chosen

theorem long_last : ∃ target : Machine, run (primitiveArrayCode (words long)) input.machine = .ok (target.push w[40]) 0 ∧
    target.mem 0 = w[105] ∧ target.mem 40 = w[64] ∧ target.mem 104 = w[64] ∧ target.mem 17 = w[7] := by
  obtain ⟨target,ran,cursor,length,old,_,contents⟩ := actual_target long (by decide +kernel) (by decide +kernel)
  exact ⟨target,ran,cursor,length,contents 63 (wmod 64) (by decide +kernel),old⟩

theorem pair_not_zeroed : observe (run (primitiveArrayCode [w[11],w[23]]) input.machine) ≠ some (40,43,2,0,0,7) := by
  rw [pair_copy]
  decide

theorem empty_code_rejected : (chosen [] (by decide) (by decide)).certificate.code ≠ [] :=
  (chosen [] (by decide) (by decide)).certificate.code_ne_nil

theorem boundary_room_refused : ¬ ((W - 2) + (2 + 1) < W) := by omega

#print axioms inhabited
#print axioms empty_copy
#print axioms pair_copy
#print axioms long_inhabited
#print axioms actual_length
#print axioms actual_contents
#print axioms actual_target
#print axioms long_last
#print axioms pair_not_zeroed
#print axioms empty_code_rejected
#print axioms boundary_room_refused
end Solidity.Backend.MemoryCopies.PrimitiveArrayControls
