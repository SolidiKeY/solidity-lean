import Solidity.Backend.MemoryCopies.TypedCapture

/-! Checked execution of the existing typed capture adapter. Actual dynamic
headers and fixed type lengths guard both endpoints before any copied write. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def captureLengthCode {R : RefTy} {E : Ty} (a : ArrTy R E) (address : Fin W) : List Instr :=
  @ArrTy.casesOn (fun _ _ _ => List Instr) R E a
    (fun {_} => [.mload address.val]) (fun {_} {n} => [.push (.val (wmod n))])

def captureEndpointCode {R : RefTy} {E : Ty} (a : ArrTy R E) (address : Fin W) (endpoint : Nat) : List Instr :=
  if endpoint < W then captureLengthCode a address ++ [.push (.val (wmod endpoint)),.gt,.iszero] ++ assertTop else [.revert]

def checkedTypedCaptureCode {H : HTy} {R Q : RefTy} {E : Ty} (base : Nat → Fin W)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (start stop offset : Nat) : List Instr :=
  if start ≤ stop then captureEndpointCode sa (base src.id) stop ++
    captureEndpointCode da (base dst.id) (offset + (stop - start)) ++ typedCaptureCode base src sa dst da start stop offset
  else [.revert]

structure CheckedCaptureCertificate : Prop where
  execute : ∀ {H : HTy} {R Q : RefTy} {E : Ty} (heap : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine →
    (∃ after target,
      MemoryOps.checkedCaptureOverwrite heap src sa dst da start stop offset = some after ∧
      run (checkedTypedCaptureCode base src sa dst da start stop offset) machine = .ok target 0 ∧
      Objects.AllocatorRepr after base frame cursor target ∧ target = {machine with mem := target.mem} ∧
      (∀ address, address < frame → target.mem address = machine.mem address) ∧
      (∀ {T : RefTy} (other : HRef H T), dst.id ≠ other.id → after.get other = heap.get other)) ∨
    (MemoryOps.checkedCaptureOverwrite heap src sa dst da start stop offset = none ∧
      run (checkedTypedCaptureCode base src sa dst da start stop offset) machine = .revert)
end Solidity.Backend.MemoryCopies
