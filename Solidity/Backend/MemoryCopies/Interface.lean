import Solidity.Evm.MemoryDefaultCompile
import Solidity.Evm.MemoryStructCopySource
import Solidity.Backend.MemoryOps.Snapshot
import Solidity.Source.Hoare

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

/-- Source half of G33, indexed by the actual expected object and fresh root.
It includes the complete run result and all nonheap state, not only a returned
pointer. It accepts any memory STy; no finite-intrinsic-type selector is used.
A compiler/representation certificate is still required separately. -/
structure SourceDefaultCertificate {E : Source.Env} {Γ : Source.RCtx}
    (fuel : Nat) (τ : Source.STy) (memory : τ.loc? = some .memory)
    (before after : Source.EMState E Γ) (root : Nat)
    (data : Source.Data E.layout τ) : Prop where
  execution : (Source.zeroVal (E := E) (Γ := Γ) fuel τ).run before =
    (.ok (.memRef memory root), after)
  frame : after = (before.1, {before.2 with heap := after.2.heap})
  growth : before.2.heap.next ≤ after.2.heap.next
  fresh : before.2.heap.next ≤ root
  object : after.2.heap.get root = some ⟨τ, data⟩
  old : ∀ address, address < before.2.heap.next →
    after.2.heap.get address = before.2.heap.get address

/-- Source half of G35.01 at the actual Source storage path and requested result
type. loadMem returns
parent data and allocates nested children; allocating the parent itself is a
separate allocRef step. This success-only record does not prove failure/timeout or layout agreement;
those remain separate obligations. Consumers must relate the requested type to
the destination memory type/layout before deriving successful allocation. -/
structure SourceStorageLoadCertificate {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (fuel : Nat) (τ : Source.STy) (path : Source.SPath)
    (before after : Source.EMState E Γ) (data : Source.Data E.layout τ) : Prop where
  execution : (Source.loadMem (E := E) (Γ := Γ) frame fuel τ path).run before =
    (.ok data, after)
  nonheap : after = (before.1, {before.2 with heap := after.2.heap})
  growth : before.2.heap.next ≤ after.2.heap.next
  old : ∀ address, address < before.2.heap.next →
    after.2.heap.get address = before.2.heap.get address

/-- Complete Source default outcome, including the exact reached state on a
halt. A timeout after allocating children must not be replaced by the initial
state. This success-or-halt specification is indexed by the expected outcome;
it neither manufactures a successful run nor changes Source admission. -/
structure SourceDefaultOutcomeCertificate {E : Source.Env} {Γ : Source.RCtx}
    (fuel : Nat) (τ : Source.STy) (before after : Source.EMState E Γ)
    (outcome : Source.R (Source.Val E.layout τ)) : Prop where
  execution : (Source.zeroVal (E := E) (Γ := Γ) fuel τ).run before = (outcome, after)
  frame : after = (before.1, {before.2 with heap := after.2.heap})
  growth : before.2.heap.next ≤ after.2.heap.next
  old : ∀ address, address < before.2.heap.next →
    after.2.heap.get address = before.2.heap.get address

/-- Complete Source storage-load outcome. The exact Halt constructor and
reached state remain visible; panic data, empty revert, timeout and stuck
results cannot be collapsed into an undifferentiated failure flag. -/
structure SourceStorageLoadOutcomeCertificate {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (fuel : Nat) (τ : Source.STy) (path : Source.SPath)
    (before after : Source.EMState E Γ)
    (outcome : Source.R (Source.Data E.layout τ)) : Prop where
  execution : (Source.loadMem (E := E) (Γ := Γ) frame fuel τ path).run before =
    (outcome, after)
  nonheap : after = (before.1, {before.2 with heap := after.2.heap})
  growth : before.2.heap.next ≤ after.2.heap.next
  old : ∀ address, address < before.2.heap.next →
    after.2.heap.get address = before.2.heap.get address

/-- Actual Source storage-to-memory root copy, not merely its loadMem data
half. The nested-load intermediate state is explicit, and loadElem must return
the freshly allocated parent. Destination memory layout/path agreement and
compiled execution are separate obligations, not assumed from this record. -/
structure SourceStorageCopyCertificate {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (fuel : Nat) (τ : Source.STy)
    (memory : τ.loc? = some .memory) (path : Source.SPath)
    (before loaded after : Source.EMState E Γ) (root : Nat)
    (data : Source.Data E.layout τ) : Prop where
  load : SourceStorageLoadCertificate frame fuel τ path before loaded data
  allocation : (Source.allocRef (E := E) (Γ := Γ) data).run loaded =
    (.ok (.memRef memory root), after)
  execution : (Source.loadElem (E := E) (Γ := Γ) frame (fuel + 1) τ path).run before =
    (.ok (.memRef memory root), after)
  fresh : before.2.heap.next ≤ root
  object : after.2.heap.get root = some ⟨τ, data⟩
  nonheap : after = (before.1, {before.2 with heap := after.2.heap})
  old : ∀ address, address < before.2.heap.next →
    after.2.heap.get address = before.2.heap.get address

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
