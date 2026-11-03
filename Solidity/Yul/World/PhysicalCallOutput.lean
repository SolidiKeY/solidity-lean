import Solidity.Yul.World.PhysicalCompletion

namespace Solidity.Yul.World.PhysicalCompletion
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.Views
open Solidity.Backend.Environment (writeBytes)

def outputCount {E Γ} (completed : Result E Γ) (capacity : Word) : Word :=
  ⟨min capacity.val completed.2.effects.returndata.length,by have bound:=capacity.isLt; omega⟩

theorem output_window {E Γ} (completed : Result E Γ) (capacity : Word) :
    returnWindow completed.2.effects.returndata 0 (outputCount completed capacity).val =
      some (callOutput completed.2.effects.returndata capacity.val) := by
  have bound : min capacity.val completed.2.effects.returndata.length ≤ completed.2.effects.returndata.length := Nat.min_le_right _ _
  simp only [returnWindow,outputCount,Nat.zero_add,bound,if_true,List.drop_zero,callOutput]
  rw [← List.take_take,List.take_length]

/-- Retain the completed call even if selected-object ownership/writeback
refuses. The Option is an adapter refusal, not an EVM exceptional halt. -/
def copyOutput {E Γ} (completed : Result E Γ)
    (same : completed.2.effects.execution=completed.1.1.1.2.ex)
    (p : Placement completed.1.1.1.2.heap) (a : Nat) (string : Bool) (old : Bytes)
    (found : completed.1.1.1.2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (m : ByteView) (offset capacity : Word) :=
  (completed,HeapWindow.copyCoupledWindow completed.2 completed.1.1.1 p a string old found
    completed.1.1.2 completed.1.2 same m offset 0 (outputCount completed capacity))

theorem copyOutput_exact {E Γ} (completed : Result E Γ)
    (same : completed.2.effects.execution=completed.1.1.1.2.ex)
    (p : Placement completed.1.1.1.2.heap) (a : Nat) (string : Bool) (old : Bytes) (found)
    (m : ByteView) (offset capacity : Word)
    (inside : offset.val+min capacity.val completed.2.effects.returndata.length ≤ old.length)
    (header : (mload m (p.address a)).val=old.length) (reads : readBytes m (p.address a+32) old.length=old) :
    copyOutput completed same p a string old found m offset capacity =
      (completed,some ((writeBytes m (p.address a+32+offset.val) (callOutput completed.2.effects.returndata capacity.val),
        withSourceHeap completed.1.1.1 (completed.1.1.1.2.heap.write a
          (heapByteData E.layout string (HeapWindow.splice old offset.val (callOutput completed.2.effects.returndata capacity.val)))
          (heap_ty_of_get _ a _ _ found))),
        (completed.1.1.2,completed.1.2),completed.2)) := by
  unfold copyOutput
  rw [HeapWindow.copyCoupledWindow_exact _ _ _ _ _ _ _ _ _ _ same _ _ _ _
    (output_window completed capacity) (by simpa only [callOutput_length] using inside) header reads]

/-- Exact untouched logical destination tail, including when capacity exceeds
available returndata. This is not a claim about callee memory. -/
theorem output_tail {E Γ} (completed : Result E Γ) (old : Bytes) (offset : Nat) (capacity : Word)
    (inside : offset+min capacity.val completed.2.effects.returndata.length ≤ old.length) :
    (HeapWindow.splice old offset (callOutput completed.2.effects.returndata capacity.val)).drop
      (offset+min capacity.val completed.2.effects.returndata.length) =
      old.drop (offset+min capacity.val completed.2.effects.returndata.length) := by
  simpa only [callOutput_length] using HeapWindow.splice_suffix old
    (callOutput completed.2.effects.returndata capacity.val) offset (by simpa only [callOutput_length] using inside)

/-- RETURNDATACOPY after completion still checks the full last-frame buffer,
including source bounds for zero size; its two physical journals stay coupled. -/
def copyAfter {E Γ} (completed : Result E Γ)
    (same : completed.2.effects.execution=completed.1.1.1.2.ex)
    (p : Placement completed.1.1.1.2.heap) (a : Nat) (string : Bool) (old : Bytes) (found)
    (m : ByteView) (offset source size : Word) :=
  (completed,HeapWindow.copyCoupledWindow completed.2 completed.1.1.1 p a string old found
    completed.1.1.2 completed.1.2 same m offset source size)

theorem copyAfter_bad_source {E Γ} (completed : Result E Γ)
    (same : completed.2.effects.execution=completed.1.1.1.2.ex)
    (p : Placement completed.1.1.1.2.heap) (a : Nat) (string : Bool) (old : Bytes) (found)
    (m : ByteView) (offset source size : Word)
    (bad : completed.2.effects.returndata.length < source.val+size.val) :
    copyAfter completed same p a string old found m offset source size = (completed,none) := by
  simp only [copyAfter,HeapWindow.copyCoupledWindow,HeapWindow.copyStateWindow,
    HeapWindow.copyMemoryWindow_source _ _ _ _ _ _ _ _ _ _ _ bad,bind,Option.bind_none,Option.map_none]

theorem copyOutput_refusal {E Γ} (completed : Result E Γ)
    (same : completed.2.effects.execution=completed.1.1.1.2.ex)
    (p : Placement completed.1.1.1.2.heap) (a : Nat) (string : Bool) (old : Bytes) (found)
    (m : ByteView) (offset capacity : Word)
    (outside : ¬ offset.val+min capacity.val completed.2.effects.returndata.length ≤ old.length) :
    copyOutput completed same p a string old found m offset capacity=(completed,none) := by
  simp only [copyOutput,HeapWindow.copyCoupledWindow,HeapWindow.copyStateWindow,
    HeapWindow.copyMemoryWindow_destination completed.2.effects completed.1.1.1.2.heap p a string old found m offset 0 (outputCount completed capacity) outside,
    bind,Option.bind_none,Option.map_none]

end Solidity.Yul.World.PhysicalCompletion
