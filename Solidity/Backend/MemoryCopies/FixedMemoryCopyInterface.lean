import Solidity.Backend.MemoryCopies.RuntimeMemoryArray
import Solidity.Backend.MemoryCopies.PrimitiveArrayLive
import Solidity.Evm.MemoryFixedStorageCopy

/-! Headerless fixed-array copying reuses the existing word loop and object
allocator. Empty fixed objects retain their positive one-cell reservation. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedPrimitiveValue (primitive : PrimTy) (count : Nat) (values : List primitive.Denote)
    (sized : values.length = count) : SVal (.ref (.fixed (.prim primitive) count)) :=
  .fixed (SVec.ofLen SVal.prim count values sized)

def fixedPrimitiveObject {H : HTy} (primitive : PrimTy) (count : Nat) (values : List primitive.Denote)
    (sized : values.length = count) : MObj H (.fixed (.prim primitive) count) := ⟨values,sized⟩

def fixedMemoryEnter (count : Nat) : List Instr :=
  allocateStructCode (max 1 count) ++ [.dup 1,.swap 2,.swap 1,.push (.val (wmod count)),.push w[0]]

def runtimeFixedMemoryCode (count : Nat) : List Instr :=
  fixedMemoryEnter count ++ [.loop copyRangeCond memoryReadRangeBody] ++ [.pop,.pop,.pop,.pop]

structure FixedMemoryCopyCertificate : Prop where
  success : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (input : HRef H (.fixed (.prim primitive) count)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine), Objects.AllocatorRepr heap base frame cursor machine →
    ∀ fits : cursor.val + max 1 count < W,
    let grown := (MVal.copyMToSt heap (T := .ref (.fixed (.prim primitive) count)) input).copyStToM heap rfl
    ∃ base' target,
      run (runtimeFixedMemoryCode count) (machine.push (.val (base input.id))) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap ∧ input.id < grown.val.id
end Solidity.Backend.MemoryCopies
