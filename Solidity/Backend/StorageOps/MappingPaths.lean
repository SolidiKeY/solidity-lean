import Solidity.Backend.StorageOps.Traversal

/-!
Mapping preservation along finite typed graph paths, including retained aliases
through arbitrarily many recursive array edges. These are operation-side laws
of the published independent graph meaning, not storage representation frames
or source admission. Clearing retains extents; copying may allocate new paths,
so its law explicitly requires a previously successful mapping read.
-/

namespace Solidity.Backend.StorageOps

open TypeGraph

/-- Default observation commutes with clear, including an absent slot. -/
theorem clear_slot_default {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (slot : Slot G T) :
    slot.clear.getD (Value.dflt T) = (slot.getD (Value.dflt T)).clear := by
  cases slot with
  | absent => exact (Value.clear_dflt T).symm
  | present v => rfl

/-- Slot copy agrees with value copy after default observation. -/
theorem overlay_slot_default {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Slot G T) :
    (old.overlay src).getD (Value.dflt T) =
      (old.getD (Value.dflt T)).overlay (src.getD (Value.dflt T)) := by
  cases src with
  | absent =>
    change old.clear.getD (Value.dflt T) =
      (old.getD (Value.dflt T)).overlay (Value.dflt T)
    rw [clear_slot_default, Value.overlay_dflt]
  | present v => rfl

private theorem clear_mapping_read_aux {n : Nat} {G : Schema n}
    {A B : TypeGraph.Ty n} (path : TypeGraph.Path G A B) (root : Value G A)
    (mapping : ∃ K V, B = TypeGraph.Ty.mapping K V) :
    root.clear.find path = root.find path := by
  induction path with
  | nil =>
    obtain ⟨K, V, equal⟩ := mapping
    subst equal
    cases root
    rfl
  | cons step rest ih =>
    cases step with
    | field position =>
      cases root with
      | node fields => exact ih (fields position) mapping
    | index i =>
      cases root with
      | array extent length live slots =>
        simp only [Value.clear, Value.find, TypeGraph.Path.read, TypeGraph.Step.get]
        by_cases allocated : i.val < extent.val
        · simp only [dif_pos allocated, Option.bind_some]
          by_cases oldLive : i.val < length.val
          · simp only [if_pos oldLive, clear_slot_default]
            exact ih _ mapping
          · simp only [if_neg oldLive]
        · simp only [dif_neg allocated, Option.bind_none]
    | fixed i =>
      cases root with
      | fixed slots =>
        simp only [Value.clear, Value.find, TypeGraph.Path.read, TypeGraph.Step.get]
        split
        · simp only [Option.bind_some, clear_slot_default]
          exact ih _ mapping
        · rfl
    | key k =>
      cases root
      rfl

/-- Clearing keeps the entire result of a mapping-path lookup, including failed
reads. Every retained extent is unchanged; no live-read assertion is made. -/
theorem clear_mapping_read {n : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    {K : PrimTy} {V : TypeGraph.Ty n} (root : Value G A)
    (path : TypeGraph.Path G A (.mapping K V)) :
    root.clear.find path = root.find path :=
  clear_mapping_read_aux path root ⟨K, V, rfl⟩

private theorem overlay_mapping_read_aux {n : Nat} {G : Schema n}
    {A B : TypeGraph.Ty n} (path : TypeGraph.Path G A B)
    (old src : Value G A) (mapping : ∃ K V, B = TypeGraph.Ty.mapping K V)
    (value : Value G B) (read : old.find path = some value) :
    (old.overlay src).find path = some value := by
  induction path with
  | nil =>
    obtain ⟨K, V, equal⟩ := mapping
    subst equal
    cases old
    cases src
    exact read
  | cons step rest ih =>
    cases step with
    | field position =>
      cases old with
      | node oldFields =>
        cases src with
        | node srcFields => exact ih (oldFields position) (srcFields position) mapping value read
    | index i =>
      cases old with
      | array oe ol oh os =>
        cases src with
        | array ne nl nh ns =>
          simp only [Value.find, TypeGraph.Path.read, TypeGraph.Step.get] at read
          by_cases allocated : i.val < oe.val
          · simp only [dif_pos allocated, Option.bind_some] at read
            have newAllocated : i.val < max oe.val nl.val :=
              Nat.lt_of_lt_of_le allocated (Nat.le_max_left _ _)
            simp only [Value.overlay, Value.find, TypeGraph.Path.read, TypeGraph.Step.get,
              dif_pos newAllocated, Option.bind_some, dif_pos allocated]
            by_cases sourceLive : i.val < nl.val
            · simp only [dif_pos sourceLive]
              rw [overlay_slot_default]
              exact ih _ _ mapping value read
            · simp only [dif_neg sourceLive]
              by_cases oldLive : i.val < ol.val
              · simp only [if_pos oldLive, clear_slot_default]
                exact (clear_mapping_read_aux rest _ mapping).trans read
              · simpa only [if_neg oldLive] using read
          · simp only [dif_neg allocated, Option.bind_none] at read
            cases read
    | fixed i =>
      cases old with
      | fixed oldSlots =>
        cases src with
        | fixed srcSlots =>
          simp only [Value.find, TypeGraph.Path.read, TypeGraph.Step.get] at read
          split at read
          next allocated =>
            simp only [Option.bind_some] at read
            simp only [Value.overlay, Value.find, TypeGraph.Path.read, TypeGraph.Step.get,
              dif_pos allocated, Option.bind_some]
            rw [overlay_slot_default]
            exact ih _ _ mapping value read
          next missing =>
            simp only [Option.bind_none] at read
            cases read
    | key k =>
      cases old
      cases src
      exact read

/-- Every previously readable mapping survives copy at the same retained path,
including recursive paths and mappings beneath shortened live tails. Copy may
allocate new paths, so a successful old read is an essential premise. -/
theorem overlay_mapping_read {n : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    {K : PrimTy} {V : TypeGraph.Ty n} (old src : Value G A)
    (path : TypeGraph.Path G A (.mapping K V)) (value : Value G (.mapping K V))
    (read : old.find path = some value) : (old.overlay src).find path = some value :=
  overlay_mapping_read_aux path old src ⟨K, V, rfl⟩ value read

/-- The runtime traversal inherits recursive mapping preservation from its
proved equality to the independent copy meaning. -/
theorem copyArray_mapping_read {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    {K : PrimTy} {V : TypeGraph.Ty n} (old src : Value G (.array E))
    (path : TypeGraph.Path G (.array E) (.mapping K V))
    (value : Value G (.mapping K V)) (read : old.find path = some value) :
    (copyArray old src).find path = some value := by
  rw [copyArray_eq_overlay]
  exact overlay_mapping_read old src path value read

/-- Deletion preserves every mapping reached beneath its destination. This
composes a real successful delete with an arbitrary recursive suffix. -/
theorem delete_mapping_below {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    {K : PrimTy} {V : TypeGraph.Ty n} (root result : Value G A)
    (dst : TypeGraph.Path G A T) (suffix : TypeGraph.Path G T (.mapping K V))
    (old : Value G T) (value : Value G (.mapping K V))
    (readDst : root.find dst = some old) (readMap : old.find suffix = some value)
    (deleted : root.delAt dst = some result) :
    result.find (dst.append suffix) = some value := by
  simp only [Value.delAt, readDst] at deleted
  have after : result.find dst = some old.clear := root.find_save result dst old.clear deleted
  change (dst.append suffix).read Value.dflt result = some value
  rw [TypeGraph.Path.read_append]
  change (result.find dst).bind (fun v => v.find suffix) = some value
  rw [after]
  change old.clear.find suffix = some value
  rw [clear_mapping_read]
  exact readMap

/-- Snapshot copying preserves mapping contents below the destination even
when the captured source and destination paths overlap. -/
theorem copyAt_mapping_below {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    {K : PrimTy} {V : TypeGraph.Ty n} (root result : Value G A)
    (dst src : TypeGraph.Path G A (.array E))
    (suffix : TypeGraph.Path G (.array E) (.mapping K V))
    (old snapshot : Value G (.array E)) (value : Value G (.mapping K V))
    (readDst : root.find dst = some old) (readSrc : root.find src = some snapshot)
    (readMap : old.find suffix = some value) (copied : copyAt root dst src = some result) :
    result.find (dst.append suffix) = some value := by
  have after := copyAt_readback root result dst src old snapshot readDst readSrc copied
  change (dst.append suffix).read Value.dflt result = some value
  rw [TypeGraph.Path.read_append]
  change (result.find dst).bind (fun v => v.find suffix) = some value
  rw [after]
  change (old.overlay snapshot).find suffix = some value
  exact overlay_mapping_read old snapshot suffix value readMap

end Solidity.Backend.StorageOps
