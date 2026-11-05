import Solidity.Backend.MemoryCopies.RangeOverlap
import Solidity.Backend.MemoryOps.CheckedSnapshot

/-! Compile the existing typed captureOverwrite using the proved overlap loop.
Array bounds and the complete represented allocator supply every word bound. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def typedCaptureCode {H : HTy} {R Q : RefTy} {E : Ty} (base : Nat → Fin W)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) : List Instr :=
  [.push (.val (wmod ((base src.id).val + Objects.header sa + start))),
   .push (.val (wmod ((base dst.id).val + Objects.header da + offset)))] ++ rangeOverlapCode (stop - start)

structure TypedCaptureCertificate : Prop where
  execute : ∀ {H : HTy} {R Q : RefTy} {E : Ty} (heap : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine →
    ∀ (hs : MemoryOps.SliceBounds (heap.len src sa) start stop)
      (hd : offset + (stop - start) ≤ heap.len dst da),
    let after := MemoryOps.captureOverwrite heap src sa dst da start stop offset hs hd
    ∃ target,
      MemoryOps.checkedCaptureOverwrite heap src sa dst da start stop offset = some after ∧
      run (typedCaptureCode base src sa dst da start stop offset) machine = .ok target 0 ∧
      Objects.AllocatorRepr after base frame cursor target ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, address < frame → target.mem address = machine.mem address) ∧
      (∀ {T : RefTy} (other : HRef H T), dst.id ≠ other.id → after.get other = heap.get other)
end Solidity.Backend.MemoryCopies
