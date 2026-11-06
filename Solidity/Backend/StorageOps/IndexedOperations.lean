import Solidity.Backend.StorageOps.CommonPrefix

/-! Partial suffix operation commutation at existing array sibling slots.
Extent checks are preserved, including retained slots and out-of-extent failure.
This is graph operation transport, not source liveness or numeric representation. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

theorem modifyAt_array_suffix {n : Nat} {G : Schema n} {E B : TypeGraph.Ty n}
    (extent : Extent) (length : Index) (le : length.val ≤ extent.val)
    (slots : Fin extent.val → Slot G E) (i : Index) (suffix : TypeGraph.Path G E B)
    (effect : Value G B → Option (Value G B)) :
    modifyAt (.array extent length le slots) (.cons (.index i) suffix) effect =
      if inside : i.val < extent.val then
        (modifySlot slots ⟨i.val, inside⟩ (fun old => modifyAt old suffix effect)).map
          (Value.array extent length le)
      else none := by
  by_cases inside : i.val < extent.val
  · simp only [modifyAt, modifySlot, Value.find, Value.save, TypeGraph.Path.read,
      TypeGraph.Path.save, TypeGraph.Step.get, TypeGraph.Step.put, dif_pos inside,
      Option.bind_eq_bind, Option.bind_some]
    cases read : suffix.read Value.dflt ((slots ⟨i.val, inside⟩).getD (Value.dflt E)) with
    | none => rfl
    | some old =>
      simp only [Option.bind_some]
      cases changed : effect old with
      | none => rfl
      | some new =>
        simp only [Option.bind_some]
        cases saved : suffix.save Value.dflt ((slots ⟨i.val, inside⟩).getD (Value.dflt E)) new <;> rfl
  · simp only [modifyAt, Value.find, TypeGraph.Path.read, TypeGraph.Step.get,
      dif_neg inside, Option.bind_eq_bind, Option.bind_none]

theorem modifyAt_fixed_suffix {n : Nat} {G : Schema n} {E B : TypeGraph.Ty n}
    (size : FixedSize) (slots : Fin size.val → Slot G E) (i : Index)
    (suffix : TypeGraph.Path G E B) (effect : Value G B → Option (Value G B)) :
    modifyAt (.fixed slots) (.cons (.fixed i) suffix) effect =
      if inside : i.val < size.val then
        (modifySlot slots ⟨i.val, inside⟩ (fun old => modifyAt old suffix effect)).map
          (Value.fixed (m := size))
      else none := by
  by_cases inside : i.val < size.val
  · simp only [modifyAt, modifySlot, Value.find, Value.save, TypeGraph.Path.read,
      TypeGraph.Path.save, TypeGraph.Step.get, TypeGraph.Step.put, dif_pos inside,
      Option.bind_eq_bind, Option.bind_some]
    cases read : suffix.read Value.dflt ((slots ⟨i.val, inside⟩).getD (Value.dflt E)) with
    | none => rfl
    | some old =>
      simp only [Option.bind_some]
      cases changed : effect old with
      | none => rfl
      | some new =>
        simp only [Option.bind_some]
        cases saved : suffix.save Value.dflt ((slots ⟨i.val, inside⟩).getD (Value.dflt E)) new <;> rfl
  · simp only [modifyAt, Value.find, TypeGraph.Path.read, TypeGraph.Step.get,
      dif_neg inside, Option.bind_eq_bind, Option.bind_none]

/-- Different raw indices commute without allocation/live/success assumptions.
Either out-of-extent access makes both actual sequences fail. -/
theorem array_suffixes_commute {n : Nat} {G : Schema n} {E B C : TypeGraph.Ty n}
    (extent : Extent) (length : Index) (le : length.val ≤ extent.val)
    (slots : Fin extent.val → Slot G E) (a b : Index) (different : a.val ≠ b.val)
    (left : TypeGraph.Path G E B) (right : TypeGraph.Path G E C)
    (f : Value G B → Option (Value G B)) (g : Value G C → Option (Value G C)) :
    (modifyAt (.array extent length le slots) (.cons (.index a) left) f).bind
      (fun root => modifyAt root (.cons (.index b) right) g) =
    (modifyAt (.array extent length le slots) (.cons (.index b) right) g).bind
      (fun root => modifyAt root (.cons (.index a) left) f) := by
  by_cases ha : a.val < extent.val <;> by_cases hb : b.val < extent.val
  · have separate : (⟨a.val, ha⟩ : Fin extent.val) ≠ ⟨b.val, hb⟩ :=
      fun equal => different (congrArg (fun index : Fin extent.val => index.val) equal)
    simp only [modifyAt_array_suffix, dif_pos ha, dif_pos hb, Option.bind_map]
    have commute := modifySlot_commute slots ⟨a.val, ha⟩ ⟨b.val, hb⟩ separate
      (fun old => modifyAt old left f) (fun old => modifyAt old right g)
    have transported := congrArg (Option.map (Value.array extent length le)) commute
    simpa only [Option.map_bind, Function.comp_def, modifyAt_array_suffix, dif_pos ha, dif_pos hb] using transported
  · simp only [modifyAt_array_suffix, dif_pos ha, dif_neg hb, Option.bind_none,
      Option.bind_map, Function.comp_def, Option.bind_fun_none]
  · simp only [modifyAt_array_suffix, dif_neg ha, dif_pos hb, Option.bind_none,
      Option.bind_map, Function.comp_def, Option.bind_fun_none]
  · simp only [modifyAt_array_suffix, dif_neg ha, dif_neg hb, Option.bind_none]

theorem fixed_suffixes_commute {n : Nat} {G : Schema n} {E B C : TypeGraph.Ty n}
    (size : FixedSize) (slots : Fin size.val → Slot G E) (a b : Index) (different : a.val ≠ b.val)
    (left : TypeGraph.Path G E B) (right : TypeGraph.Path G E C)
    (f : Value G B → Option (Value G B)) (g : Value G C → Option (Value G C)) :
    (modifyAt (.fixed slots) (.cons (.fixed a) left) f).bind
      (fun root => modifyAt root (.cons (.fixed b) right) g) =
    (modifyAt (.fixed slots) (.cons (.fixed b) right) g).bind
      (fun root => modifyAt root (.cons (.fixed a) left) f) := by
  by_cases ha : a.val < size.val <;> by_cases hb : b.val < size.val
  · have separate : (⟨a.val, ha⟩ : Fin size.val) ≠ ⟨b.val, hb⟩ :=
      fun equal => different (congrArg (fun index : Fin size.val => index.val) equal)
    simp only [modifyAt_fixed_suffix, dif_pos ha, dif_pos hb, Option.bind_map]
    have commute := modifySlot_commute slots ⟨a.val, ha⟩ ⟨b.val, hb⟩ separate
      (fun old => modifyAt old left f) (fun old => modifyAt old right g)
    have transported := congrArg (Option.map (Value.fixed (m := size))) commute
    simpa only [Option.map_bind, Function.comp_def, modifyAt_fixed_suffix, dif_pos ha, dif_pos hb] using transported
  · simp only [modifyAt_fixed_suffix, dif_pos ha, dif_neg hb, Option.bind_none,
      Option.bind_map, Function.comp_def, Option.bind_fun_none]
  · simp only [modifyAt_fixed_suffix, dif_neg ha, dif_pos hb, Option.bind_none,
      Option.bind_map, Function.comp_def, Option.bind_fun_none]
  · simp only [modifyAt_fixed_suffix, dif_neg ha, dif_neg hb, Option.bind_none]

/-- Dynamic-array sibling partial effects beneath any finite common prefix. -/
theorem common_prefix_array_commute {n : Nat} {G : Schema n} {A E B C : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A (.array E))
    (a b : Index) (different : a.val ≠ b.val)
    (left : TypeGraph.Path G E B) (right : TypeGraph.Path G E C)
    (f : Value G B → Option (Value G B)) (g : Value G C → Option (Value G C)) :
    (modifyAt root (pre.append (.cons (.index a) left)) f).bind
      (fun next => modifyAt next (pre.append (.cons (.index b) right)) g) =
    (modifyAt root (pre.append (.cons (.index b) right)) g).bind
      (fun next => modifyAt next (pre.append (.cons (.index a) left)) f) := by
  simp only [modifyAt_append]
  apply common_prefix_lift
  intro child
  cases child with
  | array extent length le slots => exact array_suffixes_commute extent length le slots a b different left right f g

/-- Fixed-array sibling partial effects beneath any finite common prefix. -/
theorem common_prefix_fixed_commute {n : Nat} {G : Schema n} {A E B C : TypeGraph.Ty n}
    {size : FixedSize} (root : Value G A) (pre : TypeGraph.Path G A (.fixed E size))
    (a b : Index) (different : a.val ≠ b.val)
    (left : TypeGraph.Path G E B) (right : TypeGraph.Path G E C)
    (f : Value G B → Option (Value G B)) (g : Value G C → Option (Value G C)) :
    (modifyAt root (pre.append (.cons (.fixed a) left)) f).bind
      (fun next => modifyAt next (pre.append (.cons (.fixed b) right)) g) =
    (modifyAt root (pre.append (.cons (.fixed b) right)) g).bind
      (fun next => modifyAt next (pre.append (.cons (.fixed a) left)) f) := by
  simp only [modifyAt_append]
  apply common_prefix_lift
  intro child
  cases child with
  | fixed slots => exact fixed_suffixes_commute size slots a b different left right f g

end Solidity.Backend.StorageOps
