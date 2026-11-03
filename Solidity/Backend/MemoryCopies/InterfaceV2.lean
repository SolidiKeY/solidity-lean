import Solidity.Evm.MemoryDefaultCompile
import Solidity.Evm.MemoryStructCopySource

/-! Version 2: capacity-conditional certificates have a concrete fitting input.
No V1 DefaultCertificate or StorageWordCertificate is used by this interface.
Keeps/freshness, dynamic lengths and list overlap correctness are existing
master theorems, not new certificate fields. See the lane document for sources.
Alias heap identity alone is not a compiled alias certificate. -/
namespace Solidity.Backend.MemoryCopies.V2
open Solidity.Evm Solidity.Evm.Memory

/-- An actual represented input that fits this cost. Requiring only cost < W
would still allow an impossible capacity antecedent at every represented cursor.
The witness therefore carries BOTH the allocator and its fitting inequality. -/
structure AllocatorWitness (cost : Nat) where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  frame : Nat
  cursor : Fin W
  machine : Machine
  represented : Objects.AllocatorRepr heap base frame cursor machine
  fits : cursor.val + cost < W

/-- Reuse the existing default compiler, with a fitting represented input that
forces its universal correctness field to have an inhabited antecedent. This is
not a total size-failure certificate, and does not exclude large Source inputs. -/
structure DefaultCertificate (R : RefTy) (hm : (Ty.ref R).mapFree = true)
    (cost : Nat) where
  builder : Objects.DefaultBuilder R hm cost
  feasible : AllocatorWitness cost

/-- The only new finite-heap obligation: roundtrip LIVE contents. Storage-only
shadow slots are stripped by the existing model. Framing and fresh identities
come from SVal.keeps_copyStToM and SVal.copyStToM_id_ge. -/
structure StorageHeapCertificate {R : RefTy} (value : SVal (.ref R))
    (hm : (Ty.ref R).mapFree = true) : Prop where
  contents : ∀ {H : HTy} (hp : Heap H),
    MVal.copyMToSt (value.copyStToM hp hm).heap (value.copyStToM hp hm).val = value.strip

/-- The resolved-value word obligation has an actual fitting input. Empty code
cannot meet its stack/result contract at that input. Actual storage-load
compilation, Source refinement and size failures remain separate obligations. -/
structure StorageWordCertificate {R : RefTy} (value : SVal (.ref R))
    (hm : (Ty.ref R).mapFree = true) (cost : Nat) where
  code : List Instr
  heap : StorageHeapCertificate value hm
  positive : 0 < cost
  feasible : AllocatorWitness cost
  correct : ∀ {H : HTy} (hp : Heap H) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (m : Machine), Objects.AllocatorRepr hp base frame cursor m →
    ∀ hs : cursor.val + cost < W,
    let g := value.copyStToM hp hm
    ∃ base' m', run code m = .ok (m'.push (.val (base' g.val.id))) 0 ∧
      Objects.AllocatorRepr g.heap base' frame ⟨cursor.val + cost, hs⟩ m' ∧
      BaseExtends H base base' ∧ m' = {m with mem := m'.mem} ∧
      (∀ addr, 0 < addr → addr < cursor.val → m'.mem addr = m.mem addr)

end Solidity.Backend.MemoryCopies.V2
