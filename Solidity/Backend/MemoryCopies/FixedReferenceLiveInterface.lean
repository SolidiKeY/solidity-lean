import Solidity.Backend.MemoryCopies.FixedReferenceStorageParent
import Solidity.Backend.MemoryCopies.PrimitiveArrayLive

/-! Signature-only live normalization for every intrinsic fixed outer array of
dynamic primitive children, including arbitrary retained storage shadows.
The proof companion supplies the certificate; this is not compiler selection,
Source admission or a physical storage-layout adequacy theorem. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedReferenceLiveChild {primitive : PrimTy} (value : SVal (.ref (.array (.prim primitive)))) :
    SVal (.ref (.array (.prim primitive))) :=
  primitiveArrayValue primitive (primitiveArrayLiveValues value) (primitive_live_bound value)

def fixedReferenceLiveRow {primitive : PrimTy} (value : SVal (.ref (.array (.prim primitive)))) :
    PrimitiveStorageRow primitive := ⟨primitiveArrayLiveValues value,primitive_live_bound value⟩

def fixedReferenceLiveRows {primitive : PrimTy} {count : Nat}
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))) : List (PrimitiveStorageRow primitive) :=
  value.view.toList.map fixedReferenceLiveRow

def fixedReferenceLiveCanonical {primitive : PrimTy} {count : Nat}
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))) :
    SVal (.ref (.fixed (.ref (.array (.prim primitive))) count)) :=
  .fixed (SVec.ofLen fixedReferenceLiveChild count value.view.toList (SVec.length_toList value.view))

structure FixedReferenceLiveCertificate {primitive : PrimTy} {size : Nat}
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) size))) : Prop where
  count : (fixedReferenceLiveRows value).length = size
  rows : (fixedReferenceLiveCanonical value).view.toList =
    (fixedReferenceLiveRows value).map (fun row => primitiveArrayValue primitive row.val row.property)
  copying : ∀ {H : HTy} (heap : Heap H),
    value.copyStToM heap rfl = (fixedReferenceLiveCanonical value).copyStToM heap rfl
  representation : ∀ (store : WordStore) (limit : Nat) (source : Slot),
    ReprAt store limit (.ref (.fixed (.ref (.array (.prim primitive))) size)) source value →
    ReprAt store limit (.ref (.fixed (.ref (.array (.prim primitive))) size)) source
      (fixedReferenceLiveCanonical value)
  contents : (fixedReferenceLiveCanonical value).strip = value.strip

end Solidity.Backend.MemoryCopies
