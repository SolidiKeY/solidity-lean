import Solidity.Backend.MemoryCopies.SingletonCopy
import Solidity.Backend.MemoryCopies.InterfaceV2Laws
import Solidity.Evm.MemoryObjectArrayExamples

/-! Nonzero uint/Boolean payloads, fresh repeated copies and reserved framing.
These are resolved-value copies, not storage-load or size-panic simulations. -/
namespace Solidity.Backend.MemoryCopies.SingletonCopyControls
open Evm Evm.Memory
private def value : PrimTy.uint.Denote := ⟨11,by decide⟩
private def seven : PrimTy.uint.Denote := ⟨7,by decide⟩
private def witness : V2.AllocatorWitness 2 :=
  ⟨_,_,_,8,⟨40,by decide⟩,_,ObjectArrayExamples.initial_allocator,by decide⟩
private def chosen : SingletonWordCopy .uint value w[11] :=
  singletonWordCopy .uint value w[11] (ReprV.uint_of rfl) witness
private def boolean : SingletonWordCopy .bool true w[1] :=
  singletonWordCopy .bool true w[1] rfl witness
private def grown := (singletonArrayValue .uint value).copyStToM witness.heap rfl
private def second := (singletonArrayValue .uint seven).copyStToM grown.heap rfl
private def observe : Evm.Out → Option (Nat × Nat × Nat × Nat × Nat)
  | .ok machine _ => match machine.stack, machine.mem 0 with
    | .val root :: _, .val cursor => match machine.mem root.val, machine.mem (root.val + 1), machine.mem 17 with
      | .val length,.val payload,.val old => some (root.val,cursor.val,length.val,payload.val,old.val)
      | _,_,_ => none
    | _,_ => none
  | _ => none

theorem word_inhabited : Nonempty (SingletonWordCopy .uint value w[11]) := ⟨chosen⟩

theorem bool_inhabited : Nonempty (SingletonWordCopy .bool true w[1]) := ⟨boolean⟩

theorem actual_uint : observe (run chosen.certificate.code witness.machine) = some (40,42,1,11,7) := by decide +kernel

theorem actual_bool : observe (run boolean.certificate.code witness.machine) = some (40,42,1,1,7) := by decide +kernel

theorem typed_contents : MVal.copyMToSt grown.heap grown.val = (singletonArrayValue .uint value).strip :=
  chosen.certificate.heap.contents witness.heap

theorem source_length : grown.heap.len grown.val .dyn = 1 := singleton_copy_length witness.heap .uint value

theorem fresh_from_old {R : RefTy} (old : HRef witness.H R) : old.id < grown.val.id :=
  Nat.lt_of_lt_of_le old.id_lt (SVal.copyStToM_id_ge witness.heap (singletonArrayValue .uint value) rfl)

theorem root_gap_inhabited : Nonempty (V2.StorageWordRootCertificate chosen.certificate) := ⟨chosen.rootGap⟩

theorem reserved_gap :
    ∃ (base' : Nat → Fin W) (target : Machine), run chosen.certificate.code witness.machine = .ok (target.push (.val witness.cursor)) 0 ∧
      Objects.Gap grown.heap base' 0 witness.frame := by
  have gap : Objects.Gap witness.heap witness.base 0 witness.frame := by
    intro R reference
    exact .inr (witness.represented.heap.owner.above reference)
  obtain ⟨base',target,ran,_,_,_,_,root,gaps⟩ :=
    chosen.rootGap.rootGap witness.heap witness.base witness.frame witness.cursor witness.machine witness.represented witness.fits
  rw [root] at ran
  exact ⟨base',target,ran,gaps 0 witness.frame gap witness.represented.free.above⟩

theorem code_nonempty : chosen.certificate.code ≠ [] := chosen.certificate.code_ne_nil

theorem cost_W_rejected : ¬ Nonempty (V2.StorageWordCertificate (singletonArrayValue .uint value) rfl W) :=
  V2.word_cost_W_impossible (singletonArrayValue .uint value) rfl

theorem two_emitted_copies :
    ∃ target, run (chosen.certificate.code ++ singletonCopyCode w[7]) witness.machine = .ok target 0 ∧
      target.stack = [w[42],w[40],w[77]] ∧ target.mem 0 = w[44] ∧
      target.mem 40 = w[1] ∧ target.mem 41 = w[11] ∧ target.mem 42 = w[1] ∧
      target.mem 43 = w[7] ∧ target.mem 17 = w[7] := by
  let first : Machine := singletonCopyMachine witness.machine (wmod 40) w[11]
  let final : Machine := singletonCopyMachine (first.push w[40]) (wmod 42) w[7]
  have runFirst : run chosen.certificate.code witness.machine = .ok (first.push w[40]) 0 := by
    rw [chosen.code]
    exact singleton_copy_run witness.machine (wmod 40) w[11] witness.represented.free.cell witness.fits
  have cell : (first.push w[40]).mem 0 = w[42] := by decide +kernel
  have runSecond : run (singletonCopyCode w[7]) (first.push w[40]) = .ok (final.push w[42]) 0 :=
    singleton_copy_run (first.push w[40]) (wmod 42) w[7] cell (by decide)
  refine ⟨final.push w[42],?_,?_⟩
  · rw [run_append_ok runFirst,runSecond]
  · decide +kernel

theorem two_source_copies : grown.val.id = 3 ∧ second.val.id = 4 ∧
    second.heap.len (grown.val.wk second.ext) .dyn = 1 ∧ second.heap.len second.val .dyn = 1 ∧
    MVal.copyMToSt second.heap (grown.val.wk second.ext) = (singletonArrayValue .uint value).strip ∧
    MVal.copyMToSt second.heap second.val = (singletonArrayValue .uint seven).strip := by decide +kernel

theorem wrong_zero_rejected : observe (run chosen.certificate.code witness.machine) ≠ some (40,42,1,0,7) := by
  rw [actual_uint]
  decide

theorem empty_code_rejected : observe (run ([] : List Instr) witness.machine) ≠ some (40,42,1,11,7) := by decide +kernel

/-- Lack of checked room is a predicate refusal, not a proved runtime panic. -/
theorem boundary_room_refused : ¬ ((wmod (W - 1)).val + 2 < W) := by decide +kernel

#print axioms word_inhabited
#print axioms bool_inhabited
#print axioms actual_uint
#print axioms actual_bool
#print axioms typed_contents
#print axioms source_length
#print axioms fresh_from_old
#print axioms root_gap_inhabited
#print axioms reserved_gap
#print axioms code_nonempty
#print axioms cost_W_rejected
#print axioms two_emitted_copies
#print axioms two_source_copies
#print axioms wrong_zero_rejected
#print axioms empty_code_rejected
#print axioms boundary_room_refused
end Solidity.Backend.MemoryCopies.SingletonCopyControls
