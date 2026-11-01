import Solidity.Yul.Views.DynamicScalarKind
import Solidity.Yul.Views.LayoutOriginReads
import Solidity.Yul.Views.LocatedRegistration

namespace Solidity.Yul.Views

/-- Layout certificate indexed by the ACTUAL declared source type. Dynamic
uint256[] owns a length HEADER here; its reference is never inline Data and
its element cells require the separate hashed-region construction. -/
inductive StorageDeclaration (E : Source.Env) : Source.STy → Type where
  | fixed {τ} (declaration : FixedDeclaration E τ) : StorageDeclaration E τ
  | uintArray : StorageDeclaration E (.array .storage (.int .u256) none)
  /-- Properly packed unsigned widths use this constructor; the full-width
  case keeps the existing uintArray certificate and legacy header visibility. -/
  | packedUnsignedArray (t : Source.IntTy) (unsigned : t.signed = false) (packed : t.bits < 256) :
      StorageDeclaration E (.array .storage (.int t) none)
  | signedArray (t : Source.IntTy) (signed : t.signed = true) :
      StorageDeclaration E (.array .storage (.int t) none)

  | scalarArray (kind : DynamicScalarKind) : StorageDeclaration E (.array .storage kind.ty none)

/-- Reuses the existing scalar cell codec, not a claim that the declared
reference type is scalar. Source.STy.cell makes this actual header uint256. -/
def uintHeaderCell (E : Source.Env) : FixedDeclaration E (.int .u256) := .scalar (.int .u256) (by rfl)

def StorageDeclaration.pack {E τ} (d : StorageDeclaration E τ) : FixedPackFn E :=
  StorageDeclaration.casesOn (motive := fun _ _ => FixedPackFn E) d
    (fun fixed => fixed.pack)
    (alignFixedPack (uintHeaderCell E).pack)
    (fun _ _ _ => alignFixedPack (uintHeaderCell E).pack)
    (fun _ _ => alignFixedPack (uintHeaderCell E).pack)
    (fun _ => alignFixedPack (uintHeaderCell E).pack)

def StorageDeclaration.paths {E τ} (d : StorageDeclaration E τ) : Source.SPath → List Source.SPath :=
  StorageDeclaration.casesOn (motive := fun _ _ => Source.SPath → List Source.SPath) d
    (fun fixed => fixed.paths) (fun p => [p]) (fun _ _ _ p => [p]) (fun _ _ p => [p]) (fun _ p => [p])

def StorageDeclaration.endByte {E τ} (d : StorageDeclaration E τ) : Nat → Nat :=
  StorageDeclaration.casesOn (motive := fun _ _ => Nat → Nat) d
    (fun fixed => fixed.endByte) (fun cursor => roundSlot ((uintHeaderCell E).endByte (roundSlot cursor)))
    (fun _ _ _ cursor => roundSlot ((uintHeaderCell E).endByte (roundSlot cursor)))
    (fun _ _ cursor => roundSlot ((uintHeaderCell E).endByte (roundSlot cursor)))
    (fun _ cursor => roundSlot ((uintHeaderCell E).endByte (roundSlot cursor)))

theorem StorageDeclaration.pack_good {E τ} (d : StorageDeclaration E τ) : FixedPackGood d.pack := by
  cases d with
  | fixed d => exact d.pack_good
  | uintArray => exact alignFixedPack_good _ (uintHeaderCell E).pack_good
  | packedUnsignedArray _ _ _ => exact alignFixedPack_good _ (uintHeaderCell E).pack_good
  | signedArray _ _ => exact alignFixedPack_good _ (uintHeaderCell E).pack_good
  | scalarArray _ => exact alignFixedPack_good _ (uintHeaderCell E).pack_good

theorem StorageDeclaration.pack_paths {E τ} (d : StorageDeclaration E τ) : FixedPackPaths d.pack d.paths := by
  cases d with
  | fixed d => exact d.pack_paths
  | uintArray => exact alignFixedPack_paths _ _ (uintHeaderCell E).pack_paths
  | packedUnsignedArray _ _ _ => exact alignFixedPack_paths _ _ (uintHeaderCell E).pack_paths
  | signedArray _ _ => exact alignFixedPack_paths _ _ (uintHeaderCell E).pack_paths
  | scalarArray _ => exact alignFixedPack_paths _ _ (uintHeaderCell E).pack_paths

theorem StorageDeclaration.pack_end {E τ} (d : StorageDeclaration E τ) : FixedPackEnd d.pack d.endByte := by
  cases d with
  | fixed d => exact d.pack_end
  | uintArray => exact alignFixedPack_end _ _ (uintHeaderCell E).pack_end
  | packedUnsignedArray _ _ _ => exact alignFixedPack_end _ _ (uintHeaderCell E).pack_end
  | signedArray _ _ => exact alignFixedPack_end _ _ (uintHeaderCell E).pack_end
  | scalarArray _ => exact alignFixedPack_end _ _ (uintHeaderCell E).pack_end

theorem dynamic_header_cell {E : Source.Env} {root : Source.DeclName}
    (declared : E.rootTy root = some (.array .storage (.int .u256) none)) :
    E.cellTy ⟨root,[]⟩ = .int .u256 := by
  simp only [Source.Env.cellTy,Source.Env.pathTy,List.foldl_nil,declared,Option.map_some,
    Source.STy.cell,Option.getD_some]

/-- Exact one-slot reservation, independent of current runtime length. -/
theorem dynamic_header_end (E : Source.Env) (cursor : Nat) :
    (StorageDeclaration.uintArray (E := E)).endByte cursor = roundSlot cursor + 32 := by
  have aligned := (roundSlot_spec cursor).2.2
  have after : (roundSlot cursor+32)%32 = 0 := by omega
  change roundSlot (packedStart (roundSlot cursor) 32 + 32) = _
  rw [packedStart,aligned]
  change roundSlot (roundSlot cursor+32) = roundSlot cursor+32
  exact roundSlot_aligned _ after

theorem StorageDeclaration.paths_typed {E τ} (d : StorageDeclaration E τ) (p : Source.SPath)
    (typed : E.pathTy p = some τ) (q : Source.SPath) (member : q ∈ d.paths p) : (E.pathTy q).isSome := by
  cases d with
  | fixed d => exact d.paths_typed p typed q member
  | uintArray =>
    have same : q = p := List.mem_singleton.mp member
    subst q
    rw [typed]
    rfl
  | packedUnsignedArray _ _ _ =>
    have same : q = p := List.mem_singleton.mp member
    subst q
    rw [typed]
    rfl
  | signedArray _ _ =>
    have same : q = p := List.mem_singleton.mp member
    subst q
    rw [typed]
    rfl

  | scalarArray _ =>
    have same : q = p := List.mem_singleton.mp member
    subst q
    rw [typed]
    rfl

end Solidity.Yul.Views
