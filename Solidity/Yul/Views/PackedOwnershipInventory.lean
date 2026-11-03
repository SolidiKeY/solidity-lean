import Solidity.Yul.Views.PackedDynamicSnapshot

namespace Solidity.Yul.Views

def ComputedStorage.unsignedSourceHeaderElements? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (entry : {entry // entry ∈ r.unsignedTrace}) : Option (List (ScalarPath E.layout (E.lay F.this))) := do
  let n ← (Source.readLen F ⟨entry.val.1,[]⟩).run s |>.1.toOption
  if bound : n < 2^256 then some ((r.unsignedHeader entry).elements fixed F.this ⟨n,bound⟩) else none

def ComputedStorage.unsignedSourceElements? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) :
    List {entry // entry ∈ r.unsignedTrace} → Option (List (ScalarPath E.layout (E.lay F.this)))
  | [] => some []
  | entry::rest => do
    let here ← r.unsignedSourceHeaderElements? F fixed s entry
    let tail ← r.unsignedSourceElements? F fixed s rest
    some (here++tail)

/-- Old live ownership is computed from ACTUAL Source.readLen at each declared
header, not from a caller-supplied inventory or proposed final raw snapshot. -/
def ComputedStorage.unsignedSourceInventory? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) :=
  (r.unsignedSourceElements? F fixed s r.unsignedTrace.attach).map (r.registrations ++ ·)

theorem ComputedStorage.unsignedSourceInventory_roots {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) (old)
    (ready : r.unsignedSourceInventory? F fixed s = some old) (c) (member : c ∈ r.registrations) : c ∈ old := by
  obtain ⟨tail,_,same⟩ := Option.map_eq_some_iff.mp ready
  rw [← same]
  exact List.mem_append_left _ member

theorem ComputedStorage.unsignedSourceHeaderElements_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m)
    (entry : {entry // entry ∈ r.unsignedTrace}) :
    r.unsignedSourceHeaderElements? F fixed s entry =
      some ((r.unsignedHeader entry).elements fixed F.this (m ((r.unsignedHeader entry).registration F.this).slot)) := by
  let h := r.unsignedHeader entry
  have member := r.unsignedHeader_member entry
  have read := h.readLen F s (m (h.registration F.this).slot) (r.bank_agreement _ member)
    (h.view_length_cell F.this _ m (view _ member))
  unfold unsignedSourceHeaderElements?
  rw [read]
  dsimp only [Except.toOption,Bind.bind,Option.bind]
  rw [dif_pos (m (h.registration F.this).slot).isLt]

theorem ComputedStorage.unsignedSourceElements_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m)
    (entries : List {entry // entry ∈ r.unsignedTrace}) :
    r.unsignedSourceElements? F fixed s entries = some (entries.flatMap (fun entry =>
      (r.unsignedHeader entry).elements fixed F.this (m ((r.unsignedHeader entry).registration F.this).slot))) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rw [unsignedSourceElements?,r.unsignedSourceHeaderElements_view F fixed s m view entry,ih]
    rfl

theorem ComputedStorage.unsignedSourceInventory_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m) :
    r.unsignedSourceInventory? F fixed s = some (r.unsignedSnapshot fixed m) := by
  unfold unsignedSourceInventory?
  rw [r.unsignedSourceElements_view F fixed s m view]
  rfl

end Solidity.Yul.Views
