import Solidity.Backend.MemoryCopies.ForwardOverlap
import Solidity.Evm.MemoryExpr

/-! A descending traversal complements the existing forward word loop.
The existing conditional emitter selects a safe direction from runtime addresses. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def backwardRangeCond : List Instr := [.push w[0],.dup 2,.gt]

def backwardReadRangeBody : List Instr :=
  [.push w[1],.swap 1,.sub] ++ memoryReadRangeBody.take 8

def backwardRangeCode (count : Nat) : List Instr :=
  [.push w[0],.push (.val (wmod count)),.loop backwardRangeCond backwardReadRangeBody,.pop,.pop,.pop,.pop]

def rangeDirectionCode : List Instr := [.dup 2,.dup 2,.gt]

def rangeOverlapCode (count : Nat) : List Instr :=
  conditionalCode rangeDirectionCode (backwardRangeCode count) (forwardRangeCode count)

structure RangeOverlapCertificate : Prop where
  execute : ∀ (machine : Machine) (source destination : Fin W) (count : Nat),
    count < W → source.val + count ≤ W → destination.val + count ≤ W →
    ∃ target,
      run (rangeOverlapCode count) ((machine.push (.val source)).push (.val destination)) = .ok target 0 ∧
      target = {machine with mem := target.mem} ∧
      (∀ index, index < count → target.mem (destination.val + index) = machine.mem (source.val + index)) ∧
      (∀ address, address < destination.val ∨ destination.val + count ≤ address → target.mem address = machine.mem address)
  listModel : ∀ (xs : List Word) (machine : Machine) (source destination : Fin W) (count : Nat),
    (∀ index word, xs[index]? = some word → machine.mem index = word) →
    xs.length ≤ W → count < W → source.val + count ≤ xs.length → destination.val + count ≤ xs.length →
    ∃ ys target,
      MemoryOps.checkedSnapshotCopy xs source.val count destination.val = some ys ∧
      run (rangeOverlapCode count) ((machine.push (.val source)).push (.val destination)) = .ok target 0 ∧
      (∀ index word, ys[index]? = some word → target.mem index = word)
end Solidity.Backend.MemoryCopies
