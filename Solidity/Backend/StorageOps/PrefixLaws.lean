import Solidity.Backend.StorageOps.PathOperations

/-! Constructor-derived operation laws for existing intrinsic common prefixes.
No put/get identity is assumed: defaulted absent slots can be materialized.
These are graph operation laws, not numeric representation or world rollback. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

private theorem slots_overwrite {K : Type} [DecidableEq K] {n : Nat} {G : Schema n}
    {T : TypeGraph.Ty n} (slots : K → Slot G T) (key : K) (a b : Value G T) :
    Slots.write (Slots.write slots key a) key b = Slots.write slots key b := by
  funext query
  by_cases equal : query = key
  · simp only [Slots.write, if_pos equal]
  · simp only [Slots.write, if_neg equal]

private theorem fields_overwrite {n : Nat} {G : Schema n} {fs : List (Name × TypeGraph.Ty n)}
    {T : TypeGraph.Ty n} (fields : TypeGraph.Fields G fs) (p : Field fs T) (a b : Value G T) :
    @Eq (TypeGraph.Fields G fs) (TypeGraph.Fields.set (TypeGraph.Fields.set fields p a) p b)
      (TypeGraph.Fields.set fields p b) := by
  funext U q
  simp only [TypeGraph.Fields.set]
  split <;> rfl

/-- A readable step accepts every replacement of its intrinsically fixed type.
This includes defaulted mappings and retained (possibly nonlive) array slots. -/
theorem step_put_exists {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (step : TypeGraph.Step G A B) (root : Value G A) (old new : Value G B)
    (read : step.get Value.dflt root = some old) : ∃ result, step.put root new = some result := by
  cases step with
  | field p => cases root; exact ⟨_, rfl⟩
  | key k => cases root; exact ⟨_, rfl⟩
  | index i =>
    cases root with
    | array extent length le slots =>
      by_cases inside : i.val < extent.val
      · simp only [TypeGraph.Step.put, dif_pos inside]; exact ⟨_, rfl⟩
      · simp only [TypeGraph.Step.get, dif_neg inside] at read; cases read
  | fixed i =>
    cases root with
    | fixed slots =>
      simp only [TypeGraph.Step.get] at read
      split at read
      · rename_i inside
        simp only [TypeGraph.Step.put, dif_pos inside]; exact ⟨_, rfl⟩
      · cases read

/-- A successful replacement leaves the step's container/bounds intact, and
another replacement overwrites it. Derived for every existing step constructor. -/
theorem step_put_overwrite {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (step : TypeGraph.Step G A B) (root result : Value G A) (a b : Value G B)
    (saved : step.put root a = some result) : step.put result b = step.put root b := by
  cases step with
  | field p =>
    cases root with
    | node fields =>
      cases saved
      exact congrArg (fun fields => some (Value.node fields)) (fields_overwrite fields p a b)
  | key k =>
    cases root with
    | mapping slots =>
      cases saved
      exact congrArg (fun slots => some (Value.mapping slots)) (slots_overwrite slots k a b)
  | index i =>
    cases root with
    | array extent length le slots =>
      simp only [TypeGraph.Step.put] at saved
      split at saved
      · rename_i inside
        cases saved
        simp only [TypeGraph.Step.put, dif_pos inside, slots_overwrite]
      · cases saved
  | fixed i =>
    cases root with
    | fixed slots =>
      simp only [TypeGraph.Step.put] at saved
      split at saved
      · rename_i inside
        cases saved
        simp only [TypeGraph.Step.put, dif_pos inside, slots_overwrite]
      · cases saved

/-- Readable prefixes accept all replacements. No success assumption on a
subsequent effect is needed, and no live-path read is inferred. -/
theorem prefix_save_exists {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (pre : TypeGraph.Path G A B) (root : Value G A) (old new : Value G B)
    (read : root.find pre = some old) : ∃ result, root.save pre new = some result := by
  induction pre with
  | nil => exact ⟨_, rfl⟩
  | cons step rest ih =>
    simp only [Value.find, TypeGraph.Path.read] at read
    cases first : step.get Value.dflt root with
    | none => simp only [first, Option.bind_none] at read; cases read
    | some child =>
      simp only [first, Option.bind_some] at read
      obtain ⟨changed, saved⟩ := ih child old new read
      obtain ⟨result, written⟩ := step_put_exists step root child changed first
      refine ⟨result, ?_⟩
      simp only [Value.save, TypeGraph.Path.save, Option.bind_eq_bind, first,
        Option.bind_some, Value.save] at saved ⊢
      rw [saved]
      exact written

/-- Prefix replacement is stable under a second replacement at that same
pre. This is replacement composition, not a frame/representation premise. -/
theorem prefix_save_overwrite {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (pre : TypeGraph.Path G A B) (root result : Value G A) (a b : Value G B)
    (saved : root.save pre a = some result) : result.save pre b = root.save pre b := by
  induction pre with
  | nil => rfl
  | cons step rest ih =>
    simp only [Value.save, TypeGraph.Path.save, Option.bind_eq_bind] at saved
    cases first : step.get Value.dflt root with
    | none => simp only [first, Option.bind_none] at saved; cases saved
    | some child =>
      cases changed : rest.save Value.dflt child a with
      | none => simp only [first, changed, Option.bind_some, Option.bind_none] at saved; cases saved
      | some next =>
        simp only [first, changed, Option.bind_some] at saved
        have readback := step.get_put Value.dflt root result next saved
        have overwritten := ih child next a b changed
        simp only [Value.save, TypeGraph.Path.save, Option.bind_eq_bind, first,
          readback, Option.bind_some]
        rw [show rest.save Value.dflt next b = rest.save Value.dflt child b from overwritten]
        cases remaining : rest.save Value.dflt child b with
        | none => rfl
        | some last => exact step_put_overwrite step root result next last saved

end Solidity.Backend.StorageOps
