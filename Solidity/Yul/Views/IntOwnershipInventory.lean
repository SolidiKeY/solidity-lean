import Solidity.Yul.Views.IntDynamicSnapshot

namespace Solidity.Yul.Views

def ComputedStorage.integerSourceHeaderElements? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (entry : {entry // entry ∈ r.integerTrace}) : Option (List (ScalarPath E.layout (E.lay F.this))) := do
  let n ← (Source.readLen F ⟨entry.val.1,[]⟩).run s |>.1.toOption
  if bound : n < 2^256 then some ((r.integerHeader entry).elements fixed F.this ⟨n,bound⟩) else none

def ComputedStorage.integerSourceElements? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) :
    List {entry // entry ∈ r.integerTrace} → Option (List (ScalarPath E.layout (E.lay F.this)))
  | [] => some []
  | entry::rest => do
    let here ← r.integerSourceHeaderElements? F fixed s entry
    let tail ← r.integerSourceElements? F fixed s rest
    some (here++tail)

/-- Old live ownership is computed from ACTUAL Source.readLen at each declared
header, not from a caller-supplied inventory or proposed final raw snapshot. -/
def ComputedStorage.integerSourceInventory? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) :=
  (r.integerSourceElements? F fixed s r.integerTrace.attach).map (r.registrations ++ ·)

theorem ComputedStorage.integerSourceInventory_roots {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) (old)
    (ready : r.integerSourceInventory? F fixed s = some old) (c) (member : c ∈ r.registrations) : c ∈ old := by
  obtain ⟨tail,_,same⟩ := Option.map_eq_some_iff.mp ready
  rw [← same]
  exact List.mem_append_left _ member

theorem ComputedStorage.integerSourceHeaderElements_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m)
    (entry : {entry // entry ∈ r.integerTrace}) :
    r.integerSourceHeaderElements? F fixed s entry =
      some ((r.integerHeader entry).elements fixed F.this (m ((r.integerHeader entry).registration F.this).slot)) := by
  let h := r.integerHeader entry
  have member := r.integerHeader_member entry
  have read := h.readLen F s (m (h.registration F.this).slot) (r.bank_agreement _ member)
    (h.view_length_cell F.this _ m (view _ member))
  unfold integerSourceHeaderElements?
  rw [read]
  dsimp only [Except.toOption,Bind.bind,Option.bind]
  rw [dif_pos (m (h.registration F.this).slot).isLt]

theorem ComputedStorage.integerSourceElements_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m)
    (entries : List {entry // entry ∈ r.integerTrace}) :
    r.integerSourceElements? F fixed s entries = some (entries.flatMap (fun entry =>
      (r.integerHeader entry).elements fixed F.this (m ((r.integerHeader entry).registration F.this).slot))) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rw [integerSourceElements?,r.integerSourceHeaderElements_view F fixed s m view entry,ih]
    rfl

theorem ComputedStorage.integerSourceInventory_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m) :
    r.integerSourceInventory? F fixed s = some (r.integerSnapshot fixed m) := by
  unfold integerSourceInventory?
  rw [r.integerSourceElements_view F fixed s m view]
  rfl

end Solidity.Yul.Views
