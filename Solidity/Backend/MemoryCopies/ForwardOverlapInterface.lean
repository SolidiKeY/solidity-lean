import Solidity.Backend.MemoryCopies.FixedMemoryCopy
import Solidity.Backend.MemoryOps.Snapshot

/-! A word-range leaf uses the existing loop, reading each source word before
writing. Forward order permits left overlap, equal addresses and disjoint ranges. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def forwardRangeCode (count : Nat) : List Instr :=
  [.push (.val (wmod count)),.push w[0],.loop copyRangeCond memoryReadRangeBody,.pop,.pop,.pop,.pop]

def ForwardReadable (source destination : Fin W) (count : Nat) : Prop :=
  destination.val ≤ source.val ∨ source.val + count ≤ destination.val

structure ForwardOverlapCertificate : Prop where
  execute : ∀ (machine : Machine) (source destination : Fin W) (count : Nat),
    count < W → source.val + count ≤ W → destination.val + count ≤ W → ForwardReadable source destination count →
    ∃ target,
      run (forwardRangeCode count) ((machine.push (.val source)).push (.val destination)) = .ok target 0 ∧
      target = {machine with mem := target.mem} ∧
      (∀ index, index < count → target.mem (destination.val + index) = machine.mem (source.val + index)) ∧
      (∀ address, address < destination.val ∨ destination.val + count ≤ address → target.mem address = machine.mem address)
  listModel : ∀ (xs : List Word) (machine : Machine) (source destination : Fin W) (count : Nat),
    (∀ index word, xs[index]? = some word → machine.mem index = word) →
    xs.length ≤ W → count < W → source.val + count ≤ xs.length → destination.val + count ≤ xs.length →
    ForwardReadable source destination count →
    ∃ ys target,
      MemoryOps.checkedSnapshotCopy xs source.val count destination.val = some ys ∧
      run (forwardRangeCode count) ((machine.push (.val source)).push (.val destination)) = .ok target 0 ∧
      (∀ index word, ys[index]? = some word → target.mem index = word)
end Solidity.Backend.MemoryCopies
