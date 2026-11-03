import Solidity.Yul.CatalogLaws

/-!
# Intrinsic local binder tables

A binder group has one positional word slot per declared name. The independent
position relation does not use executable lookup. Completeness requires distinct
names; enclosing no-shadow checks additionally use `Fresh` against all visible
names, including names unavailable for capture.
-/
namespace Solidity.Yul

/-- Mapping a typed payload preserves lexical lookup, including its priority. -/
theorem resolve_map {α β : Type} (f : α → β) (env : List (String × α)) (name : String) :
    resolve (env.map (fun p => (p.1, f p.2))) name = (resolve env name).map f := by
  induction env with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨key, value⟩
      change (if name = key then some (f value) else _) =
        (if name = key then some value else _).map f
      by_cases h : name = key
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h]; exact ih

/-- Source-order positions of a newly declared group, before older slots. -/
def localBindings : (names : List String) → List (String × Fin names.length)
  | [] => []
  | key :: rest => (key, ⟨0, Nat.zero_lt_succ _⟩) :: (localBindings rest).map (fun p => (p.1, p.2.succ))

/-- Independent name-at-position relation for a binder group. -/
inductive Named : (names : List String) → Fin names.length → String → Prop where
  | head {key rest} : Named (key :: rest) ⟨0, Nat.zero_lt_succ _⟩ key
  | tail {key rest i name} : Named rest i name → Named (key :: rest) i.succ name

theorem Named.mem {names i name} (d : Named names i name) : name ∈ names := by
  induction d with
  | head => exact List.mem_cons_self
  | tail _ ih => exact List.mem_cons_of_mem _ ih

/-- Lookup never manufactures a binder position, even before freshness checking. -/
theorem localBindings_sound {names : List String} {name : String} {i : Fin names.length}
    (h : resolve (localBindings names) name = some i) : Named names i name := by
  induction names with
  | nil => cases h
  | cons key rest ih =>
      change (if name = key then some 0 else
        resolve ((localBindings rest).map (fun p => (p.1, p.2.succ))) name) = some i at h
      split at h
      · next he => subst name; cases h; exact .head
      · rw [resolve_map] at h
        rcases Option.map_eq_some_iff.mp h with ⟨j, hj, hji⟩
        cases hji
        exact .tail (ih hj)

/-- Every distinct declared name is found at its exact source-order slot. -/
theorem Named.complete {names i name} (d : Named names i name) :
    names.Nodup → resolve (localBindings names) name = some i := by
  induction d with
  | head => intro _; exact if_pos rfl
  | @tail key rest i name d ih =>
      intro hn
      have hs := List.nodup_cons.mp hn
      have hne : name ≠ key := by
        intro he
        exact hs.1 (he ▸ d.mem)
      change (if name = key then some 0 else
        resolve ((localBindings rest).map (fun p => (p.1, p.2.succ))) name) = _
      rw [if_neg hne, resolve_map, ih hs.2]
      rfl

theorem localBindings_iff {names : List String} (hn : names.Nodup)
    (name : String) (i : Fin names.length) :
    resolve (localBindings names) name = some i ↔ Named names i name :=
  ⟨localBindings_sound, fun d => d.complete hn⟩

/-- A binder group occupies the leading slots; old locals shift by its length. -/
def extendLocals {n : Nat} (names : List String) (old : List (String × Fin n)) :
    List (String × Fin (names.length + n)) :=
  (localBindings names).map (fun p => (p.1, p.2.castAdd n)) ++
    old.map (fun p => (p.1, Fin.natAdd names.length p.2))

/-- Successful lookup in a prefix is unaffected by a later table. -/
theorem resolve_append_some {α : Type} {left right : List (String × α)}
    {name : String} {v : α} (h : resolve left name = some v) :
    resolve (left ++ right) name = some v := by
  induction left with
  | nil => cases h
  | cons p rest ih =>
      rcases p with ⟨key, value⟩
      change (if name = key then some value else resolve rest name) = some v at h
      change (if name = key then some value else resolve (rest ++ right) name) = some v
      by_cases he : name = key
      · rw [if_pos he] at h ⊢; exact h
      · rw [if_neg he] at h ⊢; exact ih h

/-- Absent prefix names leave the suffix lookup intact. -/
theorem resolve_append_none {α : Type} {left right : List (String × α)}
    {name : String} (h : resolve left name = none) :
    resolve (left ++ right) name = resolve right name := by
  induction left with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨key, value⟩
      change (if name = key then some value else resolve rest name) = none at h
      change (if name = key then some value else resolve (rest ++ right) name) = _
      by_cases he : name = key
      · rw [if_pos he] at h; cases h
      · rw [if_neg he] at h ⊢; exact ih h

/-- A fresh group's own declared slot survives extending the local table. -/
theorem extendLocals_new {n : Nat} {names : List String} {name : String}
    {i : Fin names.length} (old : List (String × Fin n))
    (hn : names.Nodup) (d : Named names i name) :
    resolve (extendLocals names old) name = some (i.castAdd n) := by
  apply resolve_append_some
  rw [resolve_map, d.complete hn]
  rfl

/-- An older name outside the new group survives at its shifted intrinsic slot. -/
theorem extendLocals_old {n : Nat} {names : List String} {name : String}
    {old : List (String × Fin n)} {i : Fin n}
    (hn : name ∉ names) (h : resolve old name = some i) :
    resolve (extendLocals names old) name = some (Fin.natAdd names.length i) := by
  have hl : resolve (localBindings names) name = none := by
    apply resolve_none_complete
    rintro ⟨j, d⟩
    exact hn (localBindings_sound (resolve_complete d)).mem
  change resolve (_ ++ _) name = _
  rw [resolve_append_none (by rw [resolve_map, hl]; rfl), resolve_map, h]
  rfl

end Solidity.Yul
