import Solidity.Evm.MemoryDefaultCompile
import Solidity.Evm.MemoryStructCopySource
import Solidity.Backend.MemoryOps.Snapshot

/-! Signature-only obligations for G33/G35 memory defaults and copies. These records are
specifications, not inhabited certificates or coverage claims. The existing
intrinsic heap, storage-copy fold and word allocator remain the only models. -/
namespace Solidity.Backend.MemoryCopies
open Solidity.Evm Solidity.Evm.Memory

/-- G33 uses the existing builder contract, including exact allocator growth,
old identity addresses, reserved-cell framing and the actual default fold. -/
structure DefaultCertificate (R : RefTy) (hm : (Ty.ref R).mapFree = true)
    (cost : Nat) where
  builder : Objects.DefaultBuilder R hm cost

/-- G35.01 heap obligations, uniform in the initial typed heap. The target
simulation is a separate obligation below; this record alone is insufficient. -/
structure StorageHeapCertificate {R : RefTy} (value : SVal (.ref R))
    (hm : (Ty.ref R).mapFree = true) : Prop where
  keeps : ∀ {H : HTy} (hp : Heap H),
    Heap.Keeps (value.copyStToM hp hm).ext hp (value.copyStToM hp hm).heap
  fresh : ∀ {H : HTy} (hp : Heap H), H.length ≤ (value.copyStToM hp hm).val.id
  contents : ∀ {H : HTy} (hp : Heap H),
    MVal.copyMToSt (value.copyStToM hp hm).heap (value.copyStToM hp hm).val = value.strip

/-- Capacity-conditional G35.01 helper contract. The input value is already
resolved. This is not a total compiler certificate: storage loads, checked size
failures and Source refinement remain additional obligations. In particular an
uninhabited capacity antecedent cannot establish total compilation. -/
structure StorageWordCertificate {R : RefTy} (value : SVal (.ref R))
    (hm : (Ty.ref R).mapFree = true) (cost : Nat) where
  code : List Instr
  heap : StorageHeapCertificate value hm
  positive : 0 < cost
  correct : ∀ {H : HTy} (hp : Heap H) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (m : Machine), Objects.AllocatorRepr hp base frame cursor m →
    ∀ hs : cursor.val + cost < W,
    let g := value.copyStToM hp hm
    ∃ base' m', run code m = .ok (m'.push (.val (base' g.val.id))) 0 ∧
      Objects.AllocatorRepr g.heap base' frame ⟨cursor.val + cost, hs⟩ m' ∧
      BaseExtends H base base' ∧ m' = {m with mem := m'.mem} ∧
      (∀ addr, 0 < addr → addr < cursor.val → m'.mem addr = m.mem addr)

/-- Dynamic lengths are observations of the actual copied parent object. -/
structure DynamicLengthCertificate {E : Ty} {n : Nat} (values : SVec E n)
    (shadow : SList E) (bound : n < 2 ^ 256)
    (hm : (Ty.ref (.array E)).mapFree = true) : Prop where
  length : ∀ {H : HTy} (hp : Heap H),
    ((SVal.array values shadow bound).copyStToM hp hm).heap.len
      ((SVal.array values shadow bound).copyStToM hp hm).val .dyn = n

/-- G35.04 aliasing retains the existing typed identity and heap. This
specification does not equate aliasing with a storage snapshot/deep copy. -/
structure AliasCertificate {H : HTy} {R : RefTy} (hp : Heap H)
    (input output : HRef H R) (after : Heap H) : Prop where
  identity : output = input
  heap : after = hp

/-- G35.04 overlap reads the complete original range. Bounds stay explicit;
invalid bounds are refusals in checkedSnapshotCopy, not successful copies. -/
structure OverlapCertificate {α : Type} (before after : List α)
    (src len dst : Nat) : Prop where
  source_bound : src + len ≤ before.length
  target_bound : dst + len ≤ before.length
  snapshot : MemoryOps.checkedSnapshotCopy before src len dst = some after
  length : after.length = before.length
  payload : (after.drop dst).take len = (before.drop src).take len

/-- The finite intrinsic heap part of G35.05 only. This does not cover the
separate guarded TypeGraph schema API, Source bytes/string, emitted code or size
failures. No total traversal claim follows from this interface fragment. -/
structure FiniteHeapTraversalCertificate where
  heap : ∀ {R : RefTy} (value : SVal (.ref R))
    (hm : (Ty.ref R).mapFree = true), StorageHeapCertificate value hm

/-- G35.04 heap deep-copy contract over the existing snapshot/copy folds.
The source snapshot is fixed by the INITIAL heap, so it cannot be replaced by
a reached destination read during overlap. This is distinct from AliasCertificate
and says nothing yet about emitted code or physical MCOPY execution. -/
structure MemoryDeepCopyHeapCertificate {H : HTy} {R : RefTy} (hp : Heap H)
    (input : HRef H R) (hm : (Ty.ref R).mapFree = true) : Prop where
  snapshot : StorageHeapCertificate (MVal.copyMToSt hp (T := .ref R) input) hm
  distinct :
    ((MVal.copyMToSt hp (T := .ref R) input).copyStToM hp hm).val.id ≠ input.id

end Solidity.Backend.MemoryCopies
