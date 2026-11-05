import Solidity.Yul.Views.DynamicHeader

namespace Solidity.Yul.Views

def DynamicHeader.elementPath {E root cursor} (_ : DynamicHeader E root cursor) (i : Nat) : Source.SPath := ⟨root,[.index i]⟩

theorem DynamicHeader.element_type {E root cursor} (h : DynamicHeader E root cursor) (i : Nat) :
    E.cellTy (h.elementPath i) = .int .u256 := by
  simp only [elementPath,Source.Env.cellTy,Source.Env.pathTy,List.foldl_cons,List.foldl_nil,h.declared,
    Option.bind_some,Source.Env.stepTy,Option.map_some,Source.STy.cell,Source.STy.isValue,if_true,Option.getD_some]

def DynamicHeader.elementLoc {E root cursor} (h : DynamicHeader E root cursor) (a : Roadmap.Address) (i : Nat) : Storage.Loc :=
  .data (.root (h.registration a).slot.val) i

/-- All indices have the actual modular EVM location. Runtime source bounds
are separate; no artificial index/fuel cap is part of this computation. -/
def DynamicHeader.element {E root cursor} (h : DynamicHeader E root cursor) (fixed : Roadmap.Evm.Fixed)
    (a : Roadmap.Address) (i : Nat) : ScalarPath E.layout (E.lay a) where
  path := h.elementPath i
  slot := ⟨(h.elementLoc a i).word (2^256) (fixedLayoutHash fixed),Nat.mod_lt _ (by decide)⟩
  field := intField .u256 0 (by decide)
  codec := (h.element_type i).symm ▸ intCodec E.layout .u256 0 (by decide)
  width := (h.element_type i).symm ▸ StorageWidth.int .u256

theorem DynamicHeader.element_word {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) :
    (h.element fixed a i).slot.val =
      (fixed.keccak (layoutPreimageBytes (.data (h.registration a).slot.val))+i) % (2^256) := by
  change (fixedLayoutHash fixed (.data ((h.registration a).slot.val % (2^256)))+i) % (2^256) = _
  rw [Nat.mod_eq_of_lt (h.registration a).slot.isLt]
  rfl

theorem DynamicHeader.element_noWrap {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat)
    (bound : fixed.keccak (layoutPreimageBytes (.data (h.registration a).slot.val))+i < 2^256) :
    (h.element fixed a i).slot.val = fixed.keccak (layoutPreimageBytes (.data (h.registration a).slot.val))+i := by
  rw [h.element_word,Nat.mod_eq_of_lt bound]

/-- The owner locate interface's OWN lmax bound is explicit, not a source
array-length exclusion: element_word above does not require it. -/
theorem DynamicHeader.owner_locate {E root cursor} (h : DynamicHeader E root cursor) (a : Roadmap.Address)
    (i : Nat) (ownerBound : i < Storage.lmax) :
    (Storage.STy.darr .word).locate (.root (h.registration a).slot.val) [.index i] = some (.word,h.elementLoc a i) := by
  simp only [Storage.STy.locate,if_pos ownerBound,Storage.STy.size,Nat.mul_one,elementLoc]

/-- Reuse the EXACT run's registered root words and preimage region premise,
not a larger guessed root prefix or global hash injectivity. -/
theorem DynamicHeader.element_ne_registered {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i L : Nat) (roots : List Nat) (ps : List Storage.Pre)
    (regions : Hash.RegionsDisjoint (2^256) L (fixedLayoutHash fixed) roots ps)
    (lengthBound : L ≤ 2^256) (offset : i < L)
    (preimage : Storage.Pre.data (h.registration a).slot.val ∈ ps)
    (r : Roadmap.Word) (registered : r.val ∈ roots) : (h.element fixed a i).slot ≠ r := by
  intro same
  have sameWord := congrArg Fin.val same
  rw [h.element_word] at sameWord
  exact regions.2 _ preimage r.val registered
    (Hash.covers_of_hit (fixedLayoutHash_lt fixed _) lengthBound offset sameWord)

theorem DynamicHeader.elements_distinct {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i j : Nat) (ib : i < 2^256) (jb : j < 2^256)
    (different : i ≠ j) : (h.element fixed a i).slot ≠ (h.element fixed a j).slot := by
  intro same
  have eq := congrArg Fin.val same
  rw [h.element_word,h.element_word] at eq
  exact different (Storage.Loc.off_eq_of_mod_eq (fixed.keccak_lt _) ib jb eq)

end Solidity.Yul.Views
