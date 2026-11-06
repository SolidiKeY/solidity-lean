import Solidity.Source.Preservation.AllocationControls

/-! A real storage-reference copy at distinct source/destination paths.
Nested arrays force allocation of the copied inner memory object. Flat byte
copies alone would not witness allocation in `storeVal`'s storage branch.
-/
namespace Solidity.Source.Preservation.StorageCopyControls
open EM

def ty : Syn .typeName := .array (.array (.elem (.int false 256 (by decide))) .none) .none
def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar ty none none none false "src" .none)
    (.cons (.stateVar ty none none none false "dst" .none) .nil))) .nil)
def E : Env := unit.env
def frame := AllocationControls.frame
def src : SPath := ⟨⟨some "C", "src"⟩, []⟩
def dst : SPath := ⟨⟨some "C", "dst"⟩, []⟩
def arrayTy : STy := .array .storage (.array .storage (.int IntTy.u256) none) none
def sourceRef : Val E.layout arrayTy := .storRef rfl src

theorem source_reference_valid (H : HeapTy) : sourceRef.RefOK E H := rfl

def seed : EM E [] Unit := do
  writeLen frame src 1
  writeLen frame (src.go (.index 0)) 2
  writeAt frame ((src.go (.index 0)).go (.index 0)) (intWrap IntTy.u256 7)
  writeAt frame ((src.go (.index 0)).go (.index 1)) (intWrap IntTy.u256 9)

def copy : EM E [] Unit := do
  seed
  storeVal frame 12 arrayTy dst sourceRef

def intNat : Val E.layout (.int IntTy.u256) → Nat
  | .int x _ => x.toNat

def observe : EM E [] (Nat × Nat × Nat × Nat × Nat) := do
  let outer ← readLen frame dst
  let inner ← readLen frame (dst.go (.index 0))
  let a ← readAt frame ((dst.go (.index 0)).go (.index 0)) (.int IntTy.u256)
  let b ← readAt frame ((dst.go (.index 0)).go (.index 1)) (.int IntTy.u256)
  pure ((← st).heap.next, outer, inner, intNat a, intNat b)

theorem copied : (((copy >>= fun _ => observe).run (.nil, St.init E)).1) =
    .ok (1, 1, 2, 7, 9) := by rfl

def selfCopy : EM E [] Nat := do
  seed
  storeVal frame 12 arrayTy src sourceRef
  pure ((← st).heap.next)

theorem self_copy : (selfCopy.run (.nil, St.init E)).1 = .ok 0 := by rfl

theorem seed_mem (H : HeapTy) : Hoare (MemOK E H) seed
    (fun _ y => MemOK E H y) (fun _ y => MemOK E H y) :=
  Hoare.bind (writeLen_mem frame src 1) fun _ =>
    Hoare.bind (writeLen_mem frame _ 2) fun _ =>
      Hoare.bind (writeAt_mem frame _ _) fun _ => writeAt_mem frame _ _

theorem copy_mem (H : HeapTy) : Hoare (MemOK E H) copy
    (fun _ y => MemOK E H y) (fun _ y => MemOK E H y) :=
  Hoare.bind (seed_mem H) fun _ => (storeOK frame 12).val H arrayTy dst sourceRef

theorem initial_mem : MemOK E (Heap.empty : Heap E.layout).ty (.nil, St.init E) :=
  ⟨⟨⟨HeapOK.empty, HeapTy.Le.refl _⟩, trivial⟩, HeapShaped.empty, HeapInner.empty⟩

theorem wrong_copy : (((copy >>= fun _ => observe).run (.nil, St.init E)).1) ≠
    .ok (0, 1, 2, 7, 9) := by rw [copied]; intro h; cases h

#print axioms copied
#print axioms copy_mem
#print axioms self_copy
end Solidity.Source.Preservation.StorageCopyControls
