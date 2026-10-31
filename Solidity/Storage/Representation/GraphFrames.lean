import Solidity.Storage.Representation.GraphLayout
import Solidity.Semantics.RecursiveStorage.Observations

/-! Exact observation frames on the committed typed graph paths. All paths
are arbitrary finite values of the existing Path family; no depth bound. -/
namespace Solidity.Storage.Representation.Graph

inductive StepApart {n : Nat} (G : TypeGraph.Schema n) :
    {A B C : TypeGraph.Ty n} → TypeGraph.Step G A B → TypeGraph.Step G A C → Prop where
  | field {i : Fin n} {B C : TypeGraph.Ty n}
      (p : TypeGraph.Field (G.fields i) B) (q : TypeGraph.Field (G.fields i) C)
      (different : p.toNat ≠ q.toNat) : StepApart G (.field p) (.field q)
  | index {E : TypeGraph.Ty n} (i j : TypeGraph.Index) (different : i ≠ j) :
      StepApart G (TypeGraph.Step.index (E := E) i) (.index j)
  | fixed {E : TypeGraph.Ty n} {m : TypeGraph.FixedSize}
      (i j : TypeGraph.Index) (different : i ≠ j) :
      StepApart G (TypeGraph.Step.fixed (E := E) (m := m) i) (.fixed j)
  | key {K : PrimTy} {V : TypeGraph.Ty n} (k k' : K.Denote) (different : k ≠ k') :
      StepApart G (TypeGraph.Step.key (V := V) k) (.key k')

/-- Distinct typed selectors preserve the other's exact subtree read,
including a failed read, implicit default, length and retained extent. -/
theorem StepApart.frame {n : Nat} {G : TypeGraph.Schema n} {A B C : TypeGraph.Ty n}
    {s : TypeGraph.Step G A B} {t : TypeGraph.Step G A C} (apart : StepApart G s t)
    (defaults : (T : TypeGraph.Ty n) → TypeGraph.Value G T)
    (root result : TypeGraph.Value G A) (new : TypeGraph.Value G B)
    (saved : s.put root new = some result) : t.get defaults result = t.get defaults root := by
  cases apart with
  | field p q different =>
    cases root with
    | node fs =>
      cases saved
      exact congrArg some (TypeGraph.Fields.get_set_other fs p q new (Ne.symm different))
  | key k k' different =>
    cases root with
    | mapping slots =>
      cases saved
      simp only [TypeGraph.Step.get]
      rw [TypeGraph.Slots.write_other slots k k' (Ne.symm different) new]
  | index i j different =>
    cases root with
    | array extent length live slots =>
      simp only [TypeGraph.Step.put] at saved
      split at saved
      next hi =>
        cases saved
        by_cases hj : j.val < extent.val
        · simp only [TypeGraph.Step.get, dif_pos hj]
          rw [TypeGraph.Slots.write_other slots ⟨i.val, hi⟩ ⟨j.val, hj⟩ (by
            intro eq
            exact different (Fin.ext (congrArg Fin.val eq).symm)) new]
        · simp only [TypeGraph.Step.get, dif_neg hj]
      next hi => cases saved
  | @fixed E m i j different =>
    cases root with
    | fixed slots =>
      simp only [TypeGraph.Step.put] at saved
      split at saved
      next hi =>
        cases saved
        by_cases hj : j.val < m.val
        · simp only [TypeGraph.Step.get, dif_pos hj]
          rw [TypeGraph.Slots.write_other slots ⟨i.val, hi⟩ ⟨j.val, hj⟩ (by
            intro eq
            exact different (Fin.ext (congrArg Fin.val eq).symm)) new]
        · simp only [TypeGraph.Step.get, dif_neg hj]
      next hi => cases saved

/-- Typed graph paths diverge at any finite depth. -/
inductive Apart {n : Nat} (G : TypeGraph.Schema n) :
    {A B C : TypeGraph.Ty n} → TypeGraph.Path G A B → TypeGraph.Path G A C → Prop where
  | fork {A B C U V : TypeGraph.Ty n} {s : TypeGraph.Step G A B} {t : TypeGraph.Step G A C}
      (head : StepApart G s t) (p : TypeGraph.Path G B U) (q : TypeGraph.Path G C V) :
      Apart G (.cons s p) (.cons t q)
  | under {A B U V : TypeGraph.Ty n} (s : TypeGraph.Step G A B)
      {p : TypeGraph.Path G B U} {q : TypeGraph.Path G B V} (tail : Apart G p q) :
      Apart G (.cons s p) (.cons s q)

/-- Recursive typed path source frame, with no runtime-depth premise. -/
theorem Apart.read_save {n : Nat} {G : TypeGraph.Schema n} {A B C : TypeGraph.Ty n}
    {p : TypeGraph.Path G A B} {q : TypeGraph.Path G A C} (apart : Apart G p q)
    (defaults : (T : TypeGraph.Ty n) → TypeGraph.Value G T)
    (root result : TypeGraph.Value G A) (new : TypeGraph.Value G B)
    (saved : p.save defaults root new = some result) :
    q.read defaults result = q.read defaults root := by
  induction apart with
  | @fork A B C U V s t head p q =>
    simp only [TypeGraph.Path.save, Option.bind_eq_bind] at saved
    cases oldRead : s.get defaults root with
    | none => simp only [oldRead, Option.bind_none] at saved; cases saved
    | some old =>
      cases innerSave : p.save defaults old new with
      | none => simp only [oldRead, innerSave, Option.bind_some, Option.bind_none] at saved; cases saved
      | some changed =>
        simp only [oldRead, innerSave, Option.bind_some] at saved
        have frame : t.get defaults result = t.get defaults root :=
          head.frame defaults root result changed saved
        simp only [TypeGraph.Path.read, frame]
  | @under A B U V s p q tail ih =>
    simp only [TypeGraph.Path.save, Option.bind_eq_bind] at saved
    cases oldRead : s.get defaults root with
    | none => simp only [oldRead, Option.bind_none] at saved; cases saved
    | some old =>
      cases innerSave : p.save defaults old new with
      | none => simp only [oldRead, innerSave, Option.bind_some, Option.bind_none] at saved; cases saved
      | some changed =>
        simp only [oldRead, innerSave, Option.bind_some] at saved
        have freshRead : s.get defaults result = some changed :=
          s.get_put defaults root result changed saved
        simp only [TypeGraph.Path.read, freshRead, oldRead, Option.bind_some]
        exact ih old changed new innerSave

/-- Exact existing graph observations are framed, including presence/failure
and retained extent; this is source semantics, not numeric extent decoding. -/
theorem Apart.observe_save {n : Nat} {G : TypeGraph.Schema n} {A B C : TypeGraph.Ty n}
    {p : TypeGraph.Path G A B} {q : TypeGraph.Path G A C} (apart : Apart G p q)
    (root result : TypeGraph.Value G A) (new : TypeGraph.Value G B)
    (saved : root.save p new = some result) : result.observe q = root.observe q := by
  unfold TypeGraph.Value.observe TypeGraph.Value.find
  exact congrArg (fun x => x.map TypeGraph.Value.head)
    (apart.read_save TypeGraph.Value.dflt root result new saved)

/-- An element put changes neither the live length nor retained extent. -/
theorem index_put_header {n : Nat} {G : TypeGraph.Schema n} {E : TypeGraph.Ty n}
    (root result : TypeGraph.Value G (.array E)) (i : TypeGraph.Index) (new : TypeGraph.Value G E)
    (saved : (TypeGraph.Step.index i).put root new = some result) : result.head = root.head := by
  cases root with
  | array extent length live slots =>
    simp only [TypeGraph.Step.put] at saved
    split at saved
    next bound => cases saved; rfl
    next bound => cases saved

/-- An arbitrary inner element save preserves its ancestor array header. -/
theorem element_save_header {n : Nat} {G : TypeGraph.Schema n} {E U : TypeGraph.Ty n}
    (root result : TypeGraph.Value G (.array E)) (i : TypeGraph.Index)
    (tail : TypeGraph.Path G E U) (new : TypeGraph.Value G U)
    (saved : root.save (.cons (.index i) tail) new = some result) : result.head = root.head := by
  change (TypeGraph.Path.cons (.index i) tail).save TypeGraph.Value.dflt root new = some result at saved
  simp only [TypeGraph.Path.save, Option.bind_eq_bind] at saved
  cases oldRead : (TypeGraph.Step.index i).get TypeGraph.Value.dflt root with
  | none => simp only [oldRead, Option.bind_none] at saved; cases saved
  | some old =>
    cases innerSave : tail.save TypeGraph.Value.dflt old new with
    | none => simp only [oldRead, innerSave, Option.bind_some, Option.bind_none] at saved; cases saved
    | some changed =>
      simp only [oldRead, innerSave, Option.bind_some] at saved
      exact index_put_header root result i changed saved

/-- A single typed child put preserves its parent's exact head observation. -/
theorem step_put_head {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (step : TypeGraph.Step G A B) (root result : TypeGraph.Value G A) (new : TypeGraph.Value G B)
    (saved : step.put root new = some result) : result.head = root.head := by
  cases step with
  | field position => cases root with | node fs => cases saved; rfl
  | key key => cases root with | mapping slots => cases saved; rfl
  | index i => exact index_put_header root result i new saved
  | fixed i =>
    cases root with
    | fixed slots =>
      simp only [TypeGraph.Step.put] at saved
      split at saved
      next bound => cases saved; rfl
      next bound => cases saved

private theorem descendant_save_head {n : Nat} {G : TypeGraph.Schema n} {A B U : TypeGraph.Ty n}
    (step : TypeGraph.Step G A B) (tail : TypeGraph.Path G B U)
    (root result : TypeGraph.Value G A) (new : TypeGraph.Value G U)
    (saved : root.save (.cons step tail) new = some result) : result.head = root.head := by
  change (TypeGraph.Path.cons step tail).save TypeGraph.Value.dflt root new = some result at saved
  simp only [TypeGraph.Path.save, Option.bind_eq_bind] at saved
  cases oldRead : step.get TypeGraph.Value.dflt root with
  | none => simp only [oldRead, Option.bind_none] at saved; cases saved
  | some old =>
    cases innerSave : tail.save TypeGraph.Value.dflt old new with
    | none => simp only [oldRead, innerSave, Option.bind_some, Option.bind_none] at saved; cases saved
    | some changed =>
      simp only [oldRead, innerSave, Option.bind_some] at saved
      exact step_put_head step root result changed saved

/-- Every strict-descendant save frames its ancestor head at arbitrary depth. -/
theorem ancestor_observation_frame {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (stem : TypeGraph.Path G A B) : ∀ {C U : TypeGraph.Ty n}
      (step : TypeGraph.Step G B C) (tail : TypeGraph.Path G C U)
      (root result : TypeGraph.Value G A) (new : TypeGraph.Value G U),
      root.save (stem.append (.cons step tail)) new = some result →
      result.observe stem = root.observe stem := by
  induction stem with
  | nil =>
    intro C U step tail root result new saved
    exact congrArg some (descendant_save_head step tail root result new saved)
  | cons s stem ih =>
    intro C U step tail root result new saved
    change (TypeGraph.Path.cons s (stem.append (.cons step tail))).save
      TypeGraph.Value.dflt root new = some result at saved
    simp only [TypeGraph.Path.save, Option.bind_eq_bind] at saved
    cases oldRead : s.get TypeGraph.Value.dflt root with
    | none => simp only [oldRead, Option.bind_none] at saved; cases saved
    | some old =>
      cases innerSave : (stem.append (.cons step tail)).save TypeGraph.Value.dflt old new with
      | none => simp only [oldRead, innerSave, Option.bind_some, Option.bind_none] at saved; cases saved
      | some changed =>
        simp only [oldRead, innerSave, Option.bind_some] at saved
        have freshRead : s.get TypeGraph.Value.dflt result = some changed :=
          s.get_put TypeGraph.Value.dflt root result changed saved
        change ((s.get TypeGraph.Value.dflt result).bind (stem.read TypeGraph.Value.dflt)).map
            TypeGraph.Value.head =
          ((s.get TypeGraph.Value.dflt root).bind (stem.read TypeGraph.Value.dflt)).map TypeGraph.Value.head
        simp only [freshRead, oldRead, Option.bind_some]
        exact ih step tail old changed new innerSave

/-- Recursive ancestor array-header frame, as a typed specialization. -/
theorem ancestor_header_frame {n : Nat} {G : TypeGraph.Schema n} {A E U : TypeGraph.Ty n}
    (stem : TypeGraph.Path G A (.array E)) (i : TypeGraph.Index) (tail : TypeGraph.Path G E U)
    (root result : TypeGraph.Value G A) (new : TypeGraph.Value G U)
    (saved : root.save (stem.append (.cons (.index i) tail)) new = some result) :
    result.observe stem = root.observe stem :=
  ancestor_observation_frame stem (.index i) tail root result new saved

end Solidity.Storage.Representation.Graph
