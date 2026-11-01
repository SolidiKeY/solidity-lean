import Solidity.Yul.Views.InventoryRealization

namespace Solidity.Yul.Views

theorem decodeInventoryUpdate_entry {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p)) (e : MixedHeapEntry p)
    (m : ByteView) (u : OwnedInventoryUpdate allocated p) (decoded : decodeInventoryUpdate allocated p es e m = some u) : u.entry = e := by
  unfold decodeInventoryUpdate at decoded
  cases dec : decodeInventoryObject p es e.ty m (p.address e.id) with
  | none => rw [dec] at decoded; cases decoded
  | some o =>
    rw [dec] at decoded
    change (if fits : o.shape.size ≤ (allocated.shape e.id).size then some ⟨e,o,fits⟩ else none) = some u at decoded
    split at decoded
    · cases decoded; rfl
    · cases decoded

theorem decodeInventoryUpdate_raw {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p)) (e : MixedHeapEntry p)
    (m : ByteView) (u : OwnedInventoryUpdate allocated p) (decoded : decodeInventoryUpdate allocated p es e m = some u) :
    u.object.image.encode m (p.address u.entry.id) = m := by
  unfold decodeInventoryUpdate at decoded
  cases dec : decodeInventoryObject p es e.ty m (p.address e.id) with
  | none => rw [dec] at decoded; cases decoded
  | some o =>
    rw [dec] at decoded
    change (if fits : o.shape.size ≤ (allocated.shape e.id).size then some ⟨e,o,fits⟩ else none) = some u at decoded
    split at decoded
    · cases decoded; exact decodeInventoryObject_raw p es e.ty m _ o dec
    · cases decoded

theorem decodeInventoryUpdates_ids {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es entries : List (MixedHeapEntry p))
    (m : ByteView) (us : List (OwnedInventoryUpdate allocated p)) (decoded : decodeInventoryUpdates allocated p es entries m = some us) :
    us.map (fun u => u.entry.id) = entries.map MixedHeapEntry.id := by
  induction entries generalizing us with
  | nil => cases decoded; rfl
  | cons e entries ih =>
    unfold decodeInventoryUpdates at decoded
    cases one : decodeInventoryUpdate allocated p es e m with
    | none => rw [one] at decoded; cases decoded
    | some u =>
      cases tail : decodeInventoryUpdates allocated p es entries m with
      | none => rw [one,tail] at decoded; cases decoded
      | some rest =>
        rw [one,tail] at decoded
        cases decoded
        simp only [List.map_cons,decodeInventoryUpdate_entry allocated p es e m u one,ih rest tail]

theorem decodeInventoryUpdates_raw {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es entries : List (MixedHeapEntry p))
    (m : ByteView) (us : List (OwnedInventoryUpdate allocated p)) (decoded : decodeInventoryUpdates allocated p es entries m = some us) :
    ∀ u ∈ us, u.object.image.encode m (p.address u.entry.id) = m := by
  induction entries generalizing us with
  | nil => cases decoded; intro u member; cases member
  | cons e entries ih =>
    unfold decodeInventoryUpdates at decoded
    cases one : decodeInventoryUpdate allocated p es e m with
    | none => rw [one] at decoded; cases decoded
    | some u =>
      cases tail : decodeInventoryUpdates allocated p es entries m with
      | none => rw [one,tail] at decoded; cases decoded
      | some rest =>
        rw [one,tail] at decoded
        cases decoded
        intro v member
        rcases List.mem_cons.mp member with eq | later
        · subst v; exact decodeInventoryUpdate_raw allocated p es e m u one
        · exact ih rest tail v later

/-- Compose concrete successful object encodings, preserving every raw byte. -/
def reencodeInventory {E : Source.Env} {origin h : Source.Heap E.layout} {allocated : Placement origin} {p : Placement h} :
    List (OwnedInventoryUpdate allocated p) → ByteView → ByteView
  | [], m => m
  | u::rest, m => u.object.image.encode (reencodeInventory rest m) (p.address u.entry.id)

theorem reencodeInventory_raw {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es entries : List (MixedHeapEntry p))
    (m : ByteView) (us : List (OwnedInventoryUpdate allocated p)) (decoded : decodeInventoryUpdates allocated p es entries m = some us) :
    reencodeInventory us m = m := by
  have all := decodeInventoryUpdates_raw allocated p es entries m us decoded
  clear decoded
  induction us with
  | nil => rfl
  | cons u rest ih =>
    rw [reencodeInventory,ih (fun v member => all v (List.mem_cons_of_mem _ member))]
    exact all u List.mem_cons_self

end Solidity.Yul.Views
