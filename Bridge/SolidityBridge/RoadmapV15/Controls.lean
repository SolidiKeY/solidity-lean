import SolidityBridge.RoadmapV15.PrefixTransport
import SolidityBridge.RoadmapV15.PremiseTransport

/-! Inhabited, negative and combined backfill controls; no EVM execution claim. -/
namespace SolidityBridge.RoadmapV15.Controls
open Solidity Solidity.Roadmap Backend.Failure.Local

private def journal (persistent transient : Nat) : Journal Nat Nat :=
  ⟨persistent, transient, ⟨[], fun _ => 0⟩⟩

example : ∃ p q : Prefix UInt8 Outcome,
    p.Le q ∧ p.events ≠ [] ∧ q.final = some (.revert [0, 255]) := by
  refine ⟨⟨[1], none⟩, ⟨[1, 255], some (.revert [0, 255])⟩, ?_, by decide, rfl⟩
  exact ⟨⟨[255], rfl⟩, .inl rfl⟩

example : (mapPrefix UInt8.toNat id
    (⟨[1, 255], some (.revert [0, 255])⟩ : Prefix UInt8 Outcome)).final =
      some (.revert [0, 255]) := rfl

example : Prefixes.Diverges (fun _ : Nat => True)
    (fun _ => mapPrefix UInt8.toNat id
      (⟨[1, 255], none⟩ : Prefix UInt8 Outcome)) :=
  (mapPrefix_diverges_iff _ _ _ _).mpr (fun _ _ => rfl)

example : ¬ Prefixes.Diverges (fun _ : Nat => True)
    (fun _ => mapPrefix UInt8.toNat id
      (⟨[1], some (.success [255])⟩ : Prefix UInt8 Outcome)) := by
  intro h
  have bad := h 0 trivial
  cases bad

example : (finish (save (journal 7 3)) (.revert [0, 255]) (journal 99 8)).persistent = 7 := rfl
example : (finish (save (journal 7 3)) (.success [0, 255]) (journal 99 8)).persistent = 99 := rfl
example : (finish (save (journal 7 3)) (.revert [0, 255]) (journal 99 8)).transient = 3 := rfl

example : (finish (save (journal 7 3)) (.revert [255]) (journal 99 8)).persistent ≠
    (finish (save (journal 6 3)) (.revert [255]) (journal 99 8)).persistent := by decide

-- Nested rollback consumes the existing owner's theorem unchanged.
example : finish (save (journal 7 3)) (.revert [0, 255])
    (finish (save (journal 9 4)) (.revert [1]) (journal 99 8)) = journal 7 3 :=
  outer_rollback (save (journal 7 3)) (save (journal 9 4)) (journal 99 8) [1] [0, 255]

example : Hash.CollisionFree (fun _ : Nat => 0) [1] := Hash.CollisionFree.singleton 1
example : Hash.CollisionFree (fun _ : Nat => 0) [2] := Hash.CollisionFree.singleton 2
-- Separate transaction premises do not establish the cumulative premise.
example : ¬ Hash.CollisionFree (fun _ : Nat => 0) ([1] ++ [2]) := by
  intro h
  have bad : (1 : Nat) = 2 := h 1 (by decide) 2 (by decide) rfl
  cases bad

example : Hash.RegionsDisjoint 16 1 (fun x : Nat => x) [0] [2] := by decide
example : ¬ Hash.RegionsDisjoint 16 1 (fun x : Nat => x) [2] [2] := by decide

-- Cross-representation journals; the second persistent component and transient
-- snapshots deliberately differ. Only the explicitly chosen observation agrees.
private def pairedJournal (persistent hidden transient : Nat) : Journal (Nat × Nat) Nat :=
  ⟨(persistent, hidden), transient, ⟨[], fun _ => 255⟩⟩

example (o : Outcome) :
    (o, (finish (save (journal 7 3)) o (journal 99 8)).persistent) =
      (o, (finish (save (pairedJournal 7 100 9)) o
        (pairedJournal 99 200 10)).persistent.1) :=
  checkpoint_observation (fun j => j.persistent) (fun j => j.persistent.1)
    (save (journal 7 3)) (save (pairedJournal 7 100 9))
    (journal 99 8) (pairedJournal 99 200 10) o rfl rfl

example :
    (mapPrefix UInt8.toNat id
      (⟨[1, 255], some (.revert [0, 255])⟩ : Prefix UInt8 Outcome)).Le
        (mapPrefix UInt8.toNat id ⟨[1, 255], some (.revert [0, 255])⟩) :=
  mapPrefix_le _ _ (Prefix.Le.refl _)

example : Prefixes.Consistent (fun _ : Nat => mapPrefix UInt8.toNat id
    (⟨[1, 255], none⟩ : Prefix UInt8 Outcome)) :=
  mapPrefix_consistent _ _ _ (fun _ _ _ => Prefix.Le.refl _)

-- Completion observes both the exact revert payload and the rolled-back value.
example : Prefixes.Completes
    (fun _ : Nat => mapPrefix UInt8.toNat id
      (⟨[1, 255], some (.revert [0, 255],
        (finish (save (journal 7 3)) (.revert [0, 255]) (journal 99 8)).persistent)⟩ :
        Prefix UInt8 (Outcome × Nat))) (.revert [0, 255], 7) :=
  mapPrefix_completes _ _ _ _ ⟨0, rfl⟩

-- Use the published actual Keccak function. Repeated nonempty preimages need
-- neither injectivity nor a global region premise. This is a test fixture only.
private def fixed : Fixed where
  evm := Evm.withKeccak
  ledger := fun bal _ a => bal a
  regionLen := 1
  rootSlots := 0

example : fixed.Sane := ⟨by decide, by decide, by decide⟩

private theorem singleton_guard : HashPremise fixed [[1, 255]] [[1, 255]] := by
  constructor
  · exact Hash.CollisionFree.singleton _
  · constructor
    · intro x hx y hy hne
      have hx' : x = [1, 255] := List.mem_singleton.mp hx
      have hy' : y = [1, 255] := List.mem_singleton.mp hy
      exact False.elim (hne (hx'.trans hy'.symm))
    · intro x hx r hr
      change r ∈ ([] : List Nat) at hr
      cases hr

private theorem repeated_guard :
    HashPremise fixed ([[1, 255]] ++ [[1, 255]]) ([[1, 255]] ++ [[1, 255]]) := by
  apply hashPremise_mono (runHashes := [[1, 255]]) (runSlots := [[1, 255]])
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx <;> exact hx
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx <;> exact hx
  · exact singleton_guard

example : HashPremise fixed [[1, 255]] [[1, 255]] :=
  hashPremise_suffix [[1, 255]] [[1, 255]] [[1, 255]] [[1, 255]] repeated_guard

#print axioms mapPrefix_le
#print axioms mapPrefix_final_none
#print axioms mapPrefix_consistent
#print axioms mapPrefix_diverges_iff
#print axioms mapPrefix_completes
#print axioms hashPremise_mono
#print axioms hashPremise_suffix
#print axioms checkpoint_relation
#print axioms checkpoint_observation
end SolidityBridge.RoadmapV15.Controls
