import Solidity.Backend.Failure.Correct

/-! Instruction-count prefixes of the actual existing packet emitter.
No new evaluator, opcode semantics, gas bound or unknown-memory encoder. -/
namespace Solidity.Backend.AbiWorld.PacketPrefix
open Failure

theorem take_split (a : Nat) (i : Input) (k r : Nat) (hk : k ≤ i.bytes.length) :
    (emit a i).take (3*k+r) = writes a (i.bytes.take k) ++
      (writes (a+k) (i.bytes.drop k) ++ [pushNat i.bytes.length,pushNat a,.op i.terminal]).take r := by
  have plen : (i.bytes.take k).length = k := by
    rw [List.length_take,Nat.min_eq_left hk]
  have split := (congrArg (writes a) (List.take_append_drop k i.bytes)).symm
  rw [writes_append,plen] at split
  have wlen : (writes a (i.bytes.take k)).length = 3*k := by rw [writes_length,plen]
  rw [emit,split,List.append_assoc,← wlen,List.take_length_add_append]

theorem take_writes (a : Nat) (i : Input) (k : Nat) (hk : k ≤ i.bytes.length) :
    (emit a i).take (3*k) = writes a (i.bytes.take k) := by
  simpa only [Nat.add_zero,List.take_zero,List.append_nil] using take_split a i k 0 hk

/-- Exact reached state after k complete byte writes, before any terminal.
This counts emitted Slice instructions, not gas or fetched EVM steps. -/
theorem boundary (a : Nat) (i : Input) (k : Nat) (hk : k ≤ i.bytes.length)
    (machine : Slice.Machine) (fits : Fits a i.bytes) (stack : machine.stack.length+2 ≤ 1024) :
    Slice.checkedRun ((emit a i).take (3*k)) machine =
      some ({machine with memory := Slice.putBytes machine.memory a (i.bytes.take k)},none) := by
  have plen : (i.bytes.take k).length = k := by rw [List.length_take,Nat.min_eq_left hk]
  have bound : a+(i.bytes.take k).length ≤ wordLimit := by have h := fits.2.2; omega
  have safe : Slice.stackSafe (writes a (i.bytes.take k)) machine = true := by
    simpa only [List.append_nil] using stackSafe_writes a (i.bytes.take k) [] machine bound stack
      (by simp only [Slice.stackSafe]; exact decide_eq_true (by omega))
  rw [take_writes a i k hk,Slice.checkedRun,safe]
  simpa only [List.append_nil,Slice.run] using run_writes a (i.bytes.take k) [] machine bound

/-- Full ordered written prefix and the untouched region are observed from
that actual reached memory; no whole-world or rollback claim. -/
theorem boundary_bytes (a : Nat) (i : Input) (k : Nat) (hk : k ≤ i.bytes.length)
    (memory : Slice.Memory) :
    Slice.getBytes (Slice.putBytes memory a (i.bytes.take k)) a k = i.bytes.take k ∧
    ∀ x, x<a ∨ a+k≤x → Slice.putBytes memory a (i.bytes.take k) x = memory x := by
  have plen : (i.bytes.take k).length = k := by rw [List.length_take,Nat.min_eq_left hk]
  constructor
  · simpa only [plen] using Slice.getBytes_putBytes memory a (i.bytes.take k)
  · intro x hx
    apply Slice.putBytes_frame
    simpa only [plen] using hx

theorem take_terminal (a : Nat) (i : Input) (r : Nat) :
    (emit a i).take (3*i.bytes.length+r) = writes a i.bytes ++
      [pushNat i.bytes.length,pushNat a,.op i.terminal].take r := by
  simpa only [List.take_length,List.drop_length,writes,List.nil_append] using
    take_split a i i.bytes.length r (Nat.le_refl _)
/-- A helper using the real reached stack-safety check, not an outcome oracle. -/
theorem checked_writes_tail (a : Nat) (bs : List UInt8) (tail : Program)
    (machine : Slice.Machine) (bound : a+bs.length ≤ wordLimit)
    (stack : machine.stack.length+2 ≤ 1024)
    (safe : Slice.stackSafe tail {machine with memory := Slice.putBytes machine.memory a bs} = true) :
    Slice.checkedRun (writes a bs ++ tail) machine =
      Slice.run tail {machine with memory := Slice.putBytes machine.memory a bs} := by
  rw [Slice.checkedRun,stackSafe_writes a bs tail machine bound stack safe]
  exact run_writes a bs tail machine bound

theorem length_push (a : Nat) (i : Input) (machine : Slice.Machine)
    (fits : Fits a i.bytes) (stack : machine.stack.length+2 ≤ 1024) :
    Slice.checkedRun ((emit a i).take (3*i.bytes.length+1)) machine =
      some ({machine with memory := Slice.putBytes machine.memory a i.bytes, stack := ⟨i.bytes.length,fits.2.1⟩ :: machine.stack},none) := by
  rw [take_terminal]
  change Slice.checkedRun (writes a i.bytes ++ [pushNat i.bytes.length]) machine = _
  rw [checked_writes_tail a i.bytes _ machine fits.2.2 stack (by
    rw [stackSafe_pushNat _ fits.2.1]
    simp only [Slice.stackSafe,List.length_cons,Bool.and_eq_true,decide_eq_true_eq]
    omega),run_pushNat _ fits.2.1]
  rfl

theorem offset_push (a : Nat) (i : Input) (machine : Slice.Machine)
    (fits : Fits a i.bytes) (stack : machine.stack.length+2 ≤ 1024) :
    Slice.checkedRun ((emit a i).take (3*i.bytes.length+2)) machine =
      some ({machine with memory := Slice.putBytes machine.memory a i.bytes, stack := ⟨a,fits.1⟩ :: ⟨i.bytes.length,fits.2.1⟩ :: machine.stack},none) := by
  rw [take_terminal]
  change Slice.checkedRun (writes a i.bytes ++ [pushNat i.bytes.length,pushNat a]) machine = _
  rw [checked_writes_tail a i.bytes _ machine fits.2.2 stack (by
    rw [stackSafe_pushNat _ fits.2.1,stackSafe_pushNat _ fits.1]
    simp only [Slice.stackSafe,List.length_cons,Bool.and_eq_true,decide_eq_true_eq]
    omega),run_pushNat _ fits.2.1,run_pushNat _ fits.1]
  rfl

/-- Both RETURN and REVERT finish only after the actual terminal instruction. -/
theorem complete (a : Nat) (i : Input) (machine : Slice.Machine)
    (fits : Fits a i.bytes) (stack : machine.stack.length+2 ≤ 1024) :
    Slice.checkedRun ((emit a i).take (3*i.bytes.length+3)) machine =
      some ({machine with memory := Slice.putBytes machine.memory a i.bytes},some i.observation) := by
  have whole : (emit a i).take (3*i.bytes.length+3) = emit a i :=
    List.take_of_length_le (by rw [emit_length]; exact Nat.le_refl _)
  rw [whole]
  simpa only [List.append_nil] using checkedRun_emit_suffix a i [] machine fits stack

/-- One pending byte has been pushed, but not stored. -/
theorem byte_push (a : Nat) (i : Input) (k : Nat) (hk : k < i.bytes.length)
    (machine : Slice.Machine) (fits : Fits a i.bytes) (stack : machine.stack.length+2 ≤ 1024) :
    Slice.checkedRun ((emit a i).take (3*k+1)) machine =
      some ({machine with memory := Slice.putBytes machine.memory a (i.bytes.take k), stack := ⟨(i.bytes[k]).toNat,byte_lt_word _⟩ :: machine.stack},none) := by
  have plen : (i.bytes.take k).length = k := by rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt hk)]
  have bound : a+(i.bytes.take k).length ≤ wordLimit := by have h := fits.2.2; omega
  have prog : (emit a i).take (3*k+1) = writes a (i.bytes.take k) ++ [pushByte i.bytes[k]] := by
    rw [take_split a i k 1 (Nat.le_of_lt hk),List.drop_eq_getElem_cons hk]
    rfl
  rw [prog,checked_writes_tail a (i.bytes.take k) _ machine bound stack (by
    rw [stackSafe_pushByte]
    simp only [Slice.stackSafe,List.length_cons,Bool.and_eq_true,decide_eq_true_eq]
    omega),run_pushByte]
  rfl

/-- Pending address is above pending byte, with no premature memory write. -/
theorem byte_offset_push (a : Nat) (i : Input) (k : Nat) (hk : k < i.bytes.length)
    (machine : Slice.Machine) (fits : Fits a i.bytes) (stack : machine.stack.length+2 ≤ 1024) :
    let ha : a+k < wordLimit := by have h := fits.2.2; omega
    Slice.checkedRun ((emit a i).take (3*k+2)) machine =
      some ({machine with memory := Slice.putBytes machine.memory a (i.bytes.take k), stack := ⟨a+k,ha⟩ :: ⟨(i.bytes[k]).toNat,byte_lt_word _⟩ :: machine.stack},none) := by
  have ha : a+k < wordLimit := by have h := fits.2.2; omega
  have plen : (i.bytes.take k).length = k := by rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt hk)]
  have bound : a+(i.bytes.take k).length ≤ wordLimit := by have h := fits.2.2; omega
  have prog : (emit a i).take (3*k+2) = writes a (i.bytes.take k) ++ [pushByte i.bytes[k],pushNat (a+k)] := by
    rw [take_split a i k 2 (Nat.le_of_lt hk),List.drop_eq_getElem_cons hk]
    rfl
  rw [prog,checked_writes_tail a (i.bytes.take k) _ machine bound stack (by
    rw [stackSafe_pushByte,stackSafe_pushNat _ ha]
    simp only [Slice.stackSafe,List.length_cons,Bool.and_eq_true,decide_eq_true_eq]
    omega),run_pushByte,run_pushNat _ ha]
  rfl
/-- Once the actual terminal is included, longer prefixes stay completed even
when their unreachable suffix would be unsupported by Slice. -/
theorem after_terminal (a : Nat) (i : Input) (tail : Program) (cut : Nat)
    (enough : 3*i.bytes.length+3 ≤ cut) (machine : Slice.Machine)
    (fits : Fits a i.bytes) (stack : machine.stack.length+2 ≤ 1024) :
    Slice.checkedRun ((emit a i ++ tail).take cut) machine =
      some ({machine with memory := Slice.putBytes machine.memory a i.bytes},some i.observation) := by
  rw [List.take_append,List.take_of_length_le (by rw [emit_length]; exact enough)]
  exact checkedRun_emit_suffix a i _ machine fits stack

end Solidity.Backend.AbiWorld.PacketPrefix
#print axioms Solidity.Backend.AbiWorld.PacketPrefix.take_split
#print axioms Solidity.Backend.AbiWorld.PacketPrefix.boundary
#print axioms Solidity.Backend.AbiWorld.PacketPrefix.boundary_bytes
#print axioms Solidity.Backend.AbiWorld.PacketPrefix.length_push
#print axioms Solidity.Backend.AbiWorld.PacketPrefix.offset_push
#print axioms Solidity.Backend.AbiWorld.PacketPrefix.byte_push
#print axioms Solidity.Backend.AbiWorld.PacketPrefix.byte_offset_push
#print axioms Solidity.Backend.AbiWorld.PacketPrefix.complete

#print axioms Solidity.Backend.AbiWorld.PacketPrefix.after_terminal
