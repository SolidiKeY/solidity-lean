import Solidity.Yul.Views.ScalarDynamicSnapshot

namespace Solidity.Yul.Views

def ComputedStorage.scalarFamilySourceHeaderElements? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (entry : {entry // entry ∈ r.scalarFamilyTrace}) : Option (List (ScalarPath E.layout (E.lay F.this))) := do
  let n ← (Source.readLen F ⟨entry.val.1,[]⟩).run s |>.1.toOption
  if bound : n < 2^256 then some ((r.scalarFamilyHeader entry).elements fixed F.this ⟨n,bound⟩) else none

def ComputedStorage.scalarFamilySourceElements? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) :
    List {entry // entry ∈ r.scalarFamilyTrace} → Option (List (ScalarPath E.layout (E.lay F.this)))
  | [] => some []
  | entry::rest => do
    let here ← r.scalarFamilySourceHeaderElements? F fixed s entry
    let tail ← r.scalarFamilySourceElements? F fixed s rest
    some (here++tail)

/-- Old live ownership is computed from ACTUAL Source.readLen at each declared
header, not from a caller-supplied inventory or proposed final raw snapshot. -/
def ComputedStorage.scalarFamilySourceInventory? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) :=
  (r.scalarFamilySourceElements? F fixed s r.scalarFamilyTrace.attach).map (r.registrations ++ ·)

theorem ComputedStorage.scalarFamilySourceInventory_roots {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) (old)
    (ready : r.scalarFamilySourceInventory? F fixed s = some old) (c) (member : c ∈ r.registrations) : c ∈ old := by
  obtain ⟨tail,_,same⟩ := Option.map_eq_some_iff.mp ready
  rw [← same]
  exact List.mem_append_left _ member

theorem ComputedStorage.scalarFamilySourceHeaderElements_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m)
    (entry : {entry // entry ∈ r.scalarFamilyTrace}) :
    r.scalarFamilySourceHeaderElements? F fixed s entry =
      some ((r.scalarFamilyHeader entry).elements fixed F.this (m ((r.scalarFamilyHeader entry).registration F.this).slot)) := by
  let h := r.scalarFamilyHeader entry
  have member := r.scalarFamilyHeader_member entry
  have read := h.readLen F s (m (h.registration F.this).slot) (r.bank_agreement _ member)
    (h.view_length_cell F.this _ m (view _ member))
  unfold scalarFamilySourceHeaderElements?
  rw [read]
  dsimp only [Except.toOption,Bind.bind,Option.bind]
  rw [dif_pos (m (h.registration F.this).slot).isLt]

theorem ComputedStorage.scalarFamilySourceElements_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m)
    (entries : List {entry // entry ∈ r.scalarFamilyTrace}) :
    r.scalarFamilySourceElements? F fixed s entries = some (entries.flatMap (fun entry =>
      (r.scalarFamilyHeader entry).elements fixed F.this (m ((r.scalarFamilyHeader entry).registration F.this).slot))) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rw [scalarFamilySourceElements?,r.scalarFamilySourceHeaderElements_view F fixed s m view entry,ih]
    rfl

theorem ComputedStorage.scalarFamilySourceInventory_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m) :
    r.scalarFamilySourceInventory? F fixed s = some (r.scalarFamilySnapshot fixed m) := by
  unfold scalarFamilySourceInventory?
  rw [r.scalarFamilySourceElements_view F fixed s m view]
  rfl

end Solidity.Yul.Views
