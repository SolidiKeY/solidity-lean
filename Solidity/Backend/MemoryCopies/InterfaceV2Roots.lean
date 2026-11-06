import Solidity.Backend.MemoryCopies.InterfaceV2

/-! Additive root and gap obligations. The published V2 certificate and its
correct field are unchanged; callers opt into this stronger companion. -/
namespace Solidity.Backend.MemoryCopies.V2
open Solidity.Evm Solidity.Evm.Memory

/-- The selected fresh root equals the input cursor and pre-existing object
 gaps remain gaps. This supplements an existing V2 word certificate. -/
structure StorageWordRootCertificate {R : RefTy} {value : SVal (.ref R)}
    {hm : (Ty.ref R).mapFree = true} {cost : Nat}
    (certificate : StorageWordCertificate value hm cost) : Prop where
  rootGap : ∀ {H : HTy} (hp : Heap H) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (m : Machine), Objects.AllocatorRepr hp base frame cursor m →
    ∀ hs : cursor.val + cost < W,
    let g := value.copyStToM hp hm
    ∃ base' m', run certificate.code m = .ok (m'.push (.val (base' g.val.id))) 0 ∧
      Objects.AllocatorRepr g.heap base' frame ⟨cursor.val + cost, hs⟩ m' ∧
      BaseExtends H base base' ∧ m' = {m with mem := m'.mem} ∧
      (∀ addr, 0 < addr → addr < cursor.val → m'.mem addr = m.mem addr) ∧
      base' g.val.id = cursor ∧
      (∀ lo hi, Objects.Gap hp base lo hi → hi ≤ cursor.val →
        Objects.Gap g.heap base' lo hi)

end Solidity.Backend.MemoryCopies.V2
