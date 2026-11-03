import Solidity.Backend.StorageOps.CommonPrefix

/-! Live-read transport for actual graph-path replacements. A retained read is
not silently promoted to a live read; before-liveness is an explicit premise.
These are graph operation laws, not numeric representation or world rollback. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

/-- A successful live step returns the same value as its logical retained read. -/
theorem step_live_get {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (step : TypeGraph.Step G A B) (root : Value G A) (old : Value G B)
    (live : step.getLive Value.dflt root = some old) : step.get Value.dflt root = some old := by
  cases step with
  | field p => exact live
  | key k => exact live
  | fixed i => exact live
  | index i =>
    cases root with
    | array extent length le slots =>
      simp only [TypeGraph.Step.getLive] at live
      split at live
      · exact live
      · cases live

/-- Replacing the selected child preserves an already-live step, because the
step's own container length/extent is unchanged by put. -/
theorem step_live_put {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (step : TypeGraph.Step G A B) (root result : Value G A) (old new : Value G B)
    (live : step.getLive Value.dflt root = some old)
    (saved : step.put root new = some result) : step.getLive Value.dflt result = some new := by
  cases step with
  | field p => exact TypeGraph.Step.get_put Value.dflt (.field p) root result new saved
  | key k => exact TypeGraph.Step.get_put Value.dflt (.key k) root result new saved
  | fixed i => exact TypeGraph.Step.get_put Value.dflt (.fixed i) root result new saved
  | index i =>
    cases root with
    | array extent length le slots =>
      simp only [TypeGraph.Step.getLive] at live
      split at live
      · rename_i inside
        have allocated : i.val < extent.val := Nat.lt_of_lt_of_le inside le
        simp only [TypeGraph.Step.put, dif_pos allocated] at saved
        cases saved
        simp only [TypeGraph.Step.getLive, if_pos inside, TypeGraph.Step.get,
          dif_pos allocated, Slots.write_self, Slot.getD]
      · cases live

/-- Every live prefix read is also the actual logical prefix read. -/
theorem prefix_live_find {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (pre : TypeGraph.Path G A B) (root : Value G A) (old : Value G B)
    (live : pre.readLive Value.dflt root = some old) : root.find pre = some old := by
  induction pre with
  | nil => exact live
  | cons step rest ih =>
    simp only [TypeGraph.Path.readLive] at live
    cases first : step.getLive Value.dflt root with
    | none => simp only [first, Option.bind_none] at live; cases live
    | some child =>
      simp only [first, Option.bind_some] at live
      simp only [Value.find, TypeGraph.Path.read, step_live_get step root child first, Option.bind_some]
      exact ih child old live

/-- An already-live prefix stays live after successful replacement at that
prefix. A merely retained prefix cannot use this theorem. -/
theorem prefix_live_save {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (pre : TypeGraph.Path G A B) (root result : Value G A) (old new : Value G B)
    (live : pre.readLive Value.dflt root = some old)
    (saved : root.save pre new = some result) : pre.readLive Value.dflt result = some new := by
  induction pre with
  | nil => cases saved; rfl
  | cons step rest ih =>
    simp only [TypeGraph.Path.readLive] at live
    cases first : step.getLive Value.dflt root with
    | none => simp only [first, Option.bind_none] at live; cases live
    | some child =>
      simp only [first, Option.bind_some] at live
      have logical := step_live_get step root child first
      simp only [Value.save, TypeGraph.Path.save, Option.bind_eq_bind, logical, Option.bind_some] at saved
      cases changed : rest.save Value.dflt child new with
      | none => simp only [changed, Option.bind_none] at saved; cases saved
      | some next =>
        simp only [changed, Option.bind_some] at saved
        have resultLive := step_live_put step root result child next first saved
        simp only [TypeGraph.Path.readLive, resultLive, Option.bind_some]
        exact ih child next old new live changed

/-- Actual live-path append composition, including failed reads. -/
theorem live_read_append {n : Nat} {G : Schema n} {A B C : TypeGraph.Ty n}
    (pre : TypeGraph.Path G A B) (suffix : TypeGraph.Path G B C) (root : Value G A) :
    (pre.append suffix).readLive Value.dflt root =
      (pre.readLive Value.dflt root).bind (suffix.readLive Value.dflt) := by
  induction pre with
  | nil => rfl
  | cons step rest ih =>
    simp only [TypeGraph.Path.append, TypeGraph.Path.readLive]
    cases first : step.getLive Value.dflt root with
    | none => rfl
    | some child => exact ih suffix child

end Solidity.Backend.StorageOps
