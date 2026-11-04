import Solidity.Backend.MemoryCopies.RuntimeStorageArray
import Solidity.Evm.MemoryStorageCopyLaws

/-! A fresh primitive-array memory copy reads the original header and live
payload through the existing machine loop. Ownership supplies separation. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def memoryReadRangeBody : List Instr :=
  [.dup 4,.dup 2,.add,.mloadAt,.dup 4,.dup 3,.add,.mstoreAt,.push w[1],.add]

def memoryReadEnter : List Instr :=
  [.dup 1,.mloadAt,.swap 1,.push w[1],.add,.swap 1,.dup 1] ++ allocateArrayCode ++
    [.dup 1,.push w[1],.add,.swap 1,.swap 3,.swap 2,.push w[0]]

def runtimeMemoryArrayCode : List Instr :=
  memoryReadEnter ++ [.loop copyRangeCond memoryReadRangeBody] ++ [.pop,.pop,.pop,.pop]

def memoryRangeMachine (machine : Machine) (index count : Nat) (destination source : Fin W) : Machine :=
  {machine with stack := [.val (wmod index),.val (wmod count),.val destination,.val source] ++ machine.stack}

structure RuntimeMemoryArrayCertificate : Prop where
  success : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy) (input : HRef H (.array (.prim primitive)))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine →
    ∀ fits : cursor.val + (heap.len input .dyn + 1) < W,
    let grown := (MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) input).copyStToM heap rfl
    ∃ base' target,
      run runtimeMemoryArrayCode (machine.push (.val (base input.id))) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (heap.len input .dyn + 1),fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap ∧ input.id < grown.val.id
end Solidity.Backend.MemoryCopies
