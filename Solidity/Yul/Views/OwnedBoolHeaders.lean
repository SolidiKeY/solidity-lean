import Solidity.Yul.Views.OwnedBoolFrame
import Solidity.Yul.Views.PrimitiveOwnershipPlan

namespace Solidity.Yul.Views

theorem representedPath_nonbool {D L} (c : ScalarPath D L) (code : BoolTrueByte)
    (notBool : L c.path≠.bool) : representedPath c code=c := by
  unfold representedPath
  rw [dif_neg notBool]

/-- Length headers are real uint256 cells, so the bool representation extension
cannot change their source reads or physical encodings. -/
theorem represented_view_nonbool {D L} (cs : List (ScalarPath D L)) (bank) (a) (encoding)
    (s : Source.Storage D L) (m : SlotView) (view : finiteView (representedRegistry cs bank a encoding) s m)
    (c : ScalarPath D L) (member : c ∈ cs) (notBool : L c.path≠.bool) :
    scalarPathView c.path c.codec c.slot s m := by
  have here := view (representedPath c (encoding.cells (ownedByteKey bank a c))) (List.mem_map.mpr ⟨c,member,rfl⟩)
  rw [representedPath_nonbool c _ notBool] at here
  exact here

theorem ComputedStorage.integerHeader_represented {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (encoding) (m : SlotView)
    (roots : ∀ c ∈ r.registrations, c ∈ cs)
    (view : finiteView (representedRegistry cs false F.this encoding) (s.2.ex.world.accounts F.this).storage m)
    (entry : {entry // entry ∈ r.integerTrace}) :
    r.integerSourceHeaderElements? F fixed s entry =
      some ((r.integerHeader entry).elements fixed F.this (m ((r.integerHeader entry).registration F.this).slot)) := by
  let h := r.integerHeader entry
  have member := r.integerHeader_member entry
  have notBool : E.lay F.this (h.registration F.this).path≠.bool := by
    change E.cellTy ⟨entry.val.1,[]⟩≠.bool
    rw [integer_dynamic_header_cell h.declared]
    intro impossible
    cases impossible
  have here := represented_view_nonbool cs false F.this encoding _ m view (h.registration F.this) (roots _ member) notBool
  have read := h.readLen F s (m (h.registration F.this).slot) (r.bank_agreement _ member) (h.view_length_cell F.this _ m here)
  unfold integerSourceHeaderElements?
  rw [read]
  dsimp only [Except.toOption,Bind.bind,Option.bind]
  rw [dif_pos (m (h.registration F.this).slot).isLt]

theorem ComputedStorage.scalarHeader_represented {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (encoding) (m : SlotView)
    (roots : ∀ c ∈ r.registrations, c ∈ cs)
    (view : finiteView (representedRegistry cs false F.this encoding) (s.2.ex.world.accounts F.this).storage m)
    (entry : {entry // entry ∈ r.scalarFamilyTrace}) :
    r.scalarFamilySourceHeaderElements? F fixed s entry =
      some ((r.scalarFamilyHeader entry).elements fixed F.this (m ((r.scalarFamilyHeader entry).registration F.this).slot)) := by
  let h := r.scalarFamilyHeader entry
  have member := r.scalarFamilyHeader_member entry
  have notBool : E.lay F.this (h.registration F.this).path≠.bool := by
    change E.cellTy ⟨entry.val.1,[]⟩≠.bool
    rw [scalarFamily_dynamic_header_cell h.declared]
    intro impossible
    cases impossible
  have here := represented_view_nonbool cs false F.this encoding _ m view (h.registration F.this) (roots _ member) notBool
  have read := h.readLen F s (m (h.registration F.this).slot) (r.bank_agreement _ member) (h.view_length_cell F.this _ m here)
  unfold scalarFamilySourceHeaderElements?
  rw [read]
  dsimp only [Except.toOption,Bind.bind,Option.bind]
  rw [dif_pos (m (h.registration F.this).slot).isLt]

theorem ComputedStorage.integerElements_represented {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (encoding) (m : SlotView)
    (roots : ∀ c ∈ r.registrations, c ∈ cs)
    (view : finiteView (representedRegistry cs false F.this encoding) (s.2.ex.world.accounts F.this).storage m)
    (entries : List {entry // entry ∈ r.integerTrace}) :
    r.integerSourceElements? F fixed s entries = some (entries.flatMap fun entry =>
      (r.integerHeader entry).elements fixed F.this (m ((r.integerHeader entry).registration F.this).slot)) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rw [integerSourceElements?,r.integerHeader_represented F fixed s cs encoding m roots view entry,ih]
    rfl

theorem ComputedStorage.scalarElements_represented {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (encoding) (m : SlotView)
    (roots : ∀ c ∈ r.registrations, c ∈ cs)
    (view : finiteView (representedRegistry cs false F.this encoding) (s.2.ex.world.accounts F.this).storage m)
    (entries : List {entry // entry ∈ r.scalarFamilyTrace}) :
    r.scalarFamilySourceElements? F fixed s entries = some (entries.flatMap fun entry =>
      (r.scalarFamilyHeader entry).elements fixed F.this (m ((r.scalarFamilyHeader entry).registration F.this).slot)) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rw [scalarFamilySourceElements?,r.scalarHeader_represented F fixed s cs encoding m roots view entry,ih]
    rfl

theorem ComputedStorage.primitiveInventory_represented {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (encoding) (m : SlotView)
    (roots : ∀ c ∈ r.registrations, c ∈ cs)
    (view : finiteView (representedRegistry cs false F.this encoding) (s.2.ex.world.accounts F.this).storage m) :
    r.primitiveSourceInventory? F fixed s=some (r.primitiveSnapshot fixed m) := by
  unfold primitiveSourceInventory?
  rw [r.integerElements_represented F fixed s cs encoding m roots view,r.scalarElements_represented F fixed s cs encoding m roots view]
  rfl

end Solidity.Yul.Views
