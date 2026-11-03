import Solidity.Yul.Views.RecursiveSnapshot

namespace Solidity.Yul.Views

def RecursiveComputedStorage.sourceHeaderElements? {E ds d active Γ} (F : Source.Fr)
    (r : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (entry : {entry // entry ∈ r.headerTrace}) : Option (List (ScalarPath E.layout (E.lay F.this))) := do
  let n ← (Source.readLen F entry.val.1).run s |>.1.toOption
  if bound : n < 2^256 then some ((r.header entry).elements fixed F.this ⟨n,bound⟩) else none

def RecursiveComputedStorage.sourceElements? {E ds d active Γ} (F : Source.Fr)
    (r : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) :
    List {entry // entry ∈ r.headerTrace} → Option (List (ScalarPath E.layout (E.lay F.this)))
  | [] => some []
  | entry::rest => do
    let here ← r.sourceHeaderElements? F fixed s entry
    let tail ← r.sourceElements? F fixed s rest
    some (here++tail)

/-- Old live ownership is computed from ACTUAL Source.readLen at each declared
header, not from a caller-supplied inventory or proposed final raw snapshot. -/
def RecursiveComputedStorage.sourceInventory? {E ds d active Γ} (F : Source.Fr)
    (r : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) :=
  (r.sourceElements? F fixed s r.headerTrace.attach).map (r.registrations ++ ·)

theorem RecursiveComputedStorage.sourceInventory_roots {E ds d active Γ} (F : Source.Fr)
    (r : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ) (old)
    (ready : r.sourceInventory? F fixed s = some old) (c) (member : c ∈ r.registrations) : c ∈ old := by
  obtain ⟨tail,_,same⟩ := Option.map_eq_some_iff.mp ready
  rw [← same]
  exact List.mem_append_left _ member

theorem RecursiveComputedStorage.sourceHeaderElements_view {E ds d active Γ} (F : Source.Fr)
    (r : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m)
    (entry : {entry // entry ∈ r.headerTrace}) :
    r.sourceHeaderElements? F fixed s entry =
      some ((r.header entry).elements fixed F.this (m ((r.header entry).registration F.this).slot)) := by
  let h := r.header entry
  have member := r.header_member entry
  have bank := r.bank_agreement _ member
  rw [PathPrimitiveHeader.registration_path] at bank
  have read := h.readLen_view F s m bank (view _ member)
  unfold sourceHeaderElements?
  rw [read]
  dsimp only [Except.toOption,Bind.bind,Option.bind]
  rw [dif_pos (m (h.registration F.this).slot).isLt]

theorem RecursiveComputedStorage.sourceElements_view {E ds d active Γ} (F : Source.Fr)
    (r : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m)
    (entries : List {entry // entry ∈ r.headerTrace}) :
    r.sourceElements? F fixed s entries = some (entries.flatMap (fun entry =>
      (r.header entry).elements fixed F.this (m ((r.header entry).registration F.this).slot))) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rw [sourceElements?,r.sourceHeaderElements_view F fixed s m view entry,ih]
    rfl

theorem RecursiveComputedStorage.sourceInventory_view {E ds d active Γ} (F : Source.Fr)
    (r : @RecursiveComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (s : Source.EMState E Γ)
    (m : SlotView) (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m) :
    r.sourceInventory? F fixed s = some (r.snapshot fixed m) := by
  unfold sourceInventory?
  rw [r.sourceElements_view F fixed s m view]
  rfl

end Solidity.Yul.Views
