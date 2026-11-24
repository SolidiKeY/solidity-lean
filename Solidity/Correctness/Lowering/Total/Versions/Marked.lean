import Solidity.Correctness.Lowering.Total.Versions.Matching

namespace Solidity.Correctness.Lowering.Total

open Solidity.Roadmap.G49Final

namespace Version
open Simulation (StateRelation Positional InitialMatching lookup_of_mem wordDenote)

/-! ## The address-aware version is sound -/

/-- A local the address-aware tables type is a primitive slot. -/
theorem localTyA_some {t : LocalTy} {τ : Source.STy} (h : Decode.localTyA t = some τ) :
    ∃ p : PrimTy, t.toLTy = .val p ∧ Prim p τ := by
  unfold Decode.localTyA at h
  split at h
  · cases h
    exact ⟨.uint, rfl, .address false⟩
  · exact localTy_some h

/-- The elementary type the address-aware tables give a state variable. -/
theorem elemA_prim {widths : List (Name × Nat)} {x : Name} {p : PrimTy} {e : Source.Elem}
    (h : Decode.elemA widths x p = some e) :
    Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage := by
  unfold Decode.elemA at h
  split at h
  · split at h
    · rename_i ok
      cases h
      rw [ok.1]
      exact ⟨.address false, rfl⟩
    · cases h
  · exact ⟨(prim_of_primElem h).1, (prim_of_primElem h).2.1⟩

/-- The address-aware unit's declaration of the state variable the model reads
under the name `x`, with the type it declares. -/
theorem stateVarsA_find (widths : List (Name × Nat)) (x : Name) (p : PrimTy) :
    (vars : List (Name × Ty)) → (parts : Source.Syn (.list (.part false))) →
    Decode.stateVarsA widths vars = some parts → Semantics.lookupBy x vars = some (.prim p) →
    ∃ e, Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage ∧
      (parts.collect (some Decode.contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some Decode.contractName && d.name == x) =
        some (Decode.varDecl x (.elem e))
  | [], _, _, hx => by cases hx
  | (y, .ref _) :: rest, _, h, _ => by simp [Decode.stateVarsA] at h
  | (y, .prim q) :: rest, parts, h, hx => by
      simp only [Decode.stateVarsA, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨e, he, parts', hp, rfl⟩ := h
      simp only [Semantics.lookupBy] at hx
      by_cases same : x = y
      · subst same
        simp only [if_true, Option.some.injEq, Ty.prim.injEq] at hx
        subst hx
        exact ⟨e, (elemA_prim he).1, (elemA_prim he).2, by simp [Source.Syn.collect, Decode.varDecl]⟩
      · simp only [if_neg same] at hx
        obtain ⟨e', prim, cell, found⟩ := stateVarsA_find widths x p rest parts' hp hx
        refine ⟨e', prim, cell, ?_⟩
        have ne : (y == x) = false := by simpa using fun h => same h.symm
        simp [Source.Syn.collect, ne, found]

/-- The address-aware tables give a unit only to contracts whose state
variables are all primitive. -/
theorem stateVarsA_prim (widths : List (Name × Nat)) : (vars : List (Name × Ty)) →
    (parts : Source.Syn (.list (.part false))) →
    Decode.stateVarsA widths vars = some parts → ∀ x U, (x, U) ∈ vars → ∃ p, U = .prim p
  | [], _, _, _, _, m => nomatch m
  | (y, .ref _) :: rest, _, h, _, _, _ => by simp [Decode.stateVarsA] at h
  | (y, .prim q) :: rest, parts, h, x, U, m => by
      simp only [Decode.stateVarsA, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨e, he, parts', hp, _⟩ := h
      rcases List.mem_cons.mp m with same | m'
      · cases same; exact ⟨q, rfl⟩
      · exact stateVarsA_prim widths rest parts' hp x U m'

/-- The address-aware tables are sound. -/
theorem soundA : Sound Decode.tablesA where
  localTy h := localTyA_some h
  cell {C u} h x U mem := by
    have h' : Decode.unitA C = some u := h
    unfold Decode.unitA at h'
    split at h'
    · simp only [Option.map_eq_some_iff] at h'
      obtain ⟨parts, hparts, rfl⟩ := h'
      obtain ⟨p, rfl⟩ := stateVarsA_prim _ _ _ hparts x U mem
      obtain ⟨e, prim, cell, found⟩ := stateVarsA_find C.widths x p C.vars parts hparts
        (lookup_of_mem _ C.vars_nodup x _ mem)
      have decl : (Source.Syn.unit (.cons (.contract false Decode.contractName .none .nil parts)
          .nil)).env.declOf .stateVar ⟨some Decode.contractName, x⟩ =
          some (Decode.varDecl x (.elem e)) := by
        simp [Source.Env.declOf, Source.Syn.env, Source.Syn.decls, Source.Syn.collect, found]
      refine ⟨p, e.ty .storage, rfl, prim, ?_⟩
      simp only [Source.Env.cellTy, Source.Env.pathTy, List.foldl_nil, Source.Env.rootTy, decl,
        Option.bind_some]
      exact congrArg (fun τ => (some τ).getD (.tuple [])) cell
    · cases h'

/-! ## Units from an element table are sound for cells -/

/-- The declaration `stateVarsOf` gives the state variable the model reads
under the name `x`, with the properties of its elementary type. -/
theorem stateVarsOf_find {el : Name → PrimTy → Option Source.Elem}
    (ok : ∀ x p e, el x p = some e → Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage)
    (x : Name) (p : PrimTy) : (vars : List (Name × Ty)) →
    (parts : Source.Syn (.list (.part false))) →
    Decode.stateVarsOf el vars = some parts → Semantics.lookupBy x vars = some (.prim p) →
    ∃ e, Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage ∧
      (parts.collect (some Decode.contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some Decode.contractName && d.name == x) =
        some (Decode.varDecl x (.elem e))
  | [], _, _, hx => by cases hx
  | (y, .ref _) :: rest, _, h, _ => by simp [Decode.stateVarsOf] at h
  | (y, .prim q) :: rest, parts, h, hx => by
      simp only [Decode.stateVarsOf, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨e, he, parts', hp, rfl⟩ := h
      simp only [Semantics.lookupBy] at hx
      by_cases same : x = y
      · subst same
        simp only [if_true, Option.some.injEq, Ty.prim.injEq] at hx
        subst hx
        exact ⟨e, (ok _ _ _ he).1, (ok _ _ _ he).2, by simp [Source.Syn.collect, Decode.varDecl]⟩
      · simp only [if_neg same] at hx
        obtain ⟨e', prim, cell, found⟩ := stateVarsOf_find ok x p rest parts' hp hx
        refine ⟨e', prim, cell, ?_⟩
        have ne : (y == x) = false := by simpa using fun h => same h.symm
        simp [Source.Syn.collect, ne, found]

/-- `stateVarsOf` succeeds only on primitive state variables. -/
theorem stateVarsOf_prim (el : Name → PrimTy → Option Source.Elem) : (vars : List (Name × Ty)) →
    (parts : Source.Syn (.list (.part false))) →
    Decode.stateVarsOf el vars = some parts → ∀ x U, (x, U) ∈ vars → ∃ p, U = .prim p
  | [], _, _, _, _, m => nomatch m
  | (y, .ref _) :: rest, _, h, _, _, _ => by simp [Decode.stateVarsOf] at h
  | (y, .prim q) :: rest, parts, h, x, U, m => by
      simp only [Decode.stateVarsOf, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨e, he, parts', hp, _⟩ := h
      rcases List.mem_cons.mp m with same | m'
      · cases same; exact ⟨q, rfl⟩
      · exact stateVarsOf_prim el rest parts' hp x U m'

/-- **A unit from an element table has primitive cells** when every
elementary type the table gives is a primitive slot's type. -/
theorem unitOf_cell {ok : Contract → Bool}
    {el : Contract → Name → PrimTy → Option Source.Elem}
    (good : ∀ C x p e, el C x p = some e →
      Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage)
    {C : Contract} {u : Source.Syn .unit} (h : Decode.unitOf ok el C = some u) (x : Name) (U : Ty)
    (mem : (x, U) ∈ C.vars) :
    ∃ (p : PrimTy) (τ : Source.STy), U = .prim p ∧ Prim p τ ∧
      u.env.cellTy ⟨⟨some Decode.contractName, x⟩, []⟩ = τ := by
  unfold Decode.unitOf at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨parts, hparts, rfl⟩ := h
    obtain ⟨p, rfl⟩ := stateVarsOf_prim _ _ _ hparts x U mem
    obtain ⟨e, prim, cell, found⟩ := stateVarsOf_find (good C) x p C.vars parts hparts
      (lookup_of_mem _ C.vars_nodup x _ mem)
    have decl : (Source.Syn.unit (.cons (.contract false Decode.contractName .none .nil parts)
        .nil)).env.declOf .stateVar ⟨some Decode.contractName, x⟩ =
        some (Decode.varDecl x (.elem e)) := by
      simp [Source.Env.declOf, Source.Syn.env, Source.Syn.decls, Source.Syn.collect, found]
    refine ⟨p, e.ty .storage, rfl, prim, ?_⟩
    simp only [Source.Env.cellTy, Source.Env.pathTy, List.foldl_nil, Source.Env.rootTy, decl,
      Option.bind_some]
    exact congrArg (fun τ => (some τ).getD (.tuple [])) cell
  · cases h

/-! ## The bytes-aware version is sound -/

/-- `bytesN` is a primitive slot's type, at either location. -/
theorem prim_of_bytesElem {n : Nat} {e : Source.Elem} (h : Decode.bytesElem n = some e) :
    Prim .uint (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage ∧
      e.ty .memory = e.ty .storage := by
  unfold Decode.bytesElem at h
  split at h
  · cases h; exact ⟨.bytes _ _, rfl, rfl⟩
  · cases h

/-- A local the bytes-aware tables type is a primitive slot. -/
theorem localTyB_some {t : LocalTy} {τ : Source.STy} (h : Decode.localTyB t = some τ) :
    ∃ p : PrimTy, t.toLTy = .val p ∧ Prim p τ := by
  unfold Decode.localTyB at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨e, he, rfl⟩ := h
      obtain ⟨prim, _, same⟩ := prim_of_bytesElem he
      exact ⟨.uint, rfl, same ▸ prim⟩
    · cases h
  · exact localTyA_some h

/-- The elementary type the bytes-aware tables give a state variable. -/
theorem elemB_prim {widths : List (Name × Nat)} {x : Name} {p : PrimTy} {e : Source.Elem}
    (h : Decode.elemB widths x p = some e) :
    Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage := by
  unfold Decode.elemB at h
  split at h
  · split at h
    · rename_i ok
      rw [ok.1]
      exact ⟨(prim_of_bytesElem h).1, (prim_of_bytesElem h).2.1⟩
    · cases h
  · exact elemA_prim h

/-- The bytes-aware tables are sound. -/
theorem soundB : Sound Decode.tablesB where
  localTy h := localTyB_some h
  cell {C u} h x U mem :=
    unitOf_cell (el := fun C => Decode.elemB C.widths) (fun _ _ _ _ he => elemB_prim he)
      (show Decode.unitB C = some u from h) x U mem

end Version

end Solidity.Correctness.Lowering.Total
