import Solidity.Yul.Views.OwnershipTransport

namespace Solidity.Yul.Views

def ComputedStorage.sourceHeaderElements? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (entry : {entry // entry ∈ r.headerTrace}) : Option (List (ScalarPath E.layout (E.lay F.this))) := do
  let n ← (Source.readLen F ⟨entry.val.1,[]⟩).run s |>.1.toOption
  if bound : n < 2^256 then some ((r.traceHeader entry).elements fixed F.this ⟨n,bound⟩) else none

def ComputedStorage.sourceElements? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) :
    List {entry // entry ∈ r.headerTrace} → Option (List (ScalarPath E.layout (E.lay F.this)))
  | [] => some []
  | entry::rest => do
    let here ← r.sourceHeaderElements? F fixed s entry
    let tail ← r.sourceElements? F fixed s rest
    some (here++tail)

/-- Old live ownership is computed from ACTUAL Source.readLen at each declared
header, not from a caller-supplied inventory or proposed final raw snapshot. -/
def ComputedStorage.sourceInventory? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) :=
  (r.sourceElements? F fixed s r.headerTrace.attach).map (r.registrations ++ ·)

theorem ComputedStorage.sourceInventory_roots {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) (old)
    (ready : r.sourceInventory? F fixed s = some old) (c) (member : c ∈ r.registrations) : c ∈ old := by
  obtain ⟨tail,_,same⟩ := Option.map_eq_some_iff.mp ready
  rw [← same]
  exact List.mem_append_left _ member

theorem ComputedStorage.sourceHeaderElements_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m)
    (entry : {entry // entry ∈ r.headerTrace}) :
    r.sourceHeaderElements? F fixed s entry =
      some ((r.traceHeader entry).elements fixed F.this (m ((r.traceHeader entry).registration F.this).slot)) := by
  let h := r.traceHeader entry
  have member := r.traceHeader_member entry
  have read := h.readLen F s (m (h.registration F.this).slot) (r.bank_agreement _ member)
    (h.view_length_cell F.this _ m (view _ member))
  unfold sourceHeaderElements?
  rw [read]
  dsimp only [Except.toOption,Bind.bind,Option.bind]
  rw [dif_pos (m (h.registration F.this).slot).isLt]

theorem ComputedStorage.sourceElements_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m)
    (entries : List {entry // entry ∈ r.headerTrace}) :
    r.sourceElements? F fixed s entries = some (entries.flatMap (fun entry =>
      (r.traceHeader entry).elements fixed F.this (m ((r.traceHeader entry).registration F.this).slot))) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rw [sourceElements?,r.sourceHeaderElements_view F fixed s m view entry,ih]
    rfl

theorem ComputedStorage.sourceInventory_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m) :
    r.sourceInventory? F fixed s = some (r.snapshotInventory fixed m) := by
  unfold sourceInventory?
  rw [r.sourceElements_view F fixed s m view]
  rfl

end Solidity.Yul.Views
