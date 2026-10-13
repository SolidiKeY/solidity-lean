import Solidity.Semantics.Storage

/-!
# Typed storage erases to untyped storage

Every typed storage operation (`Semantics/Storage.lean`) erases to its
untyped namesake in `Semantics.lean`, which is therefore never `undef` on an
erased input: each lemma reads `untyped op (erase x) = toRes erase (typed op
x)`, and `toRes` has no `undef`.  This is the storage half of a typed step
read on the erasure (`Semantics/TypedErase.lean`, M4b).

A struct is copied member by member in order (solc), and the untyped
`overlay` looks each member up by name, which agrees because a struct's
members have distinct names (`structDef_nodup`: solc refuses a struct that
repeats one, and so does the elaborator, decision 16).

`SVal.ofU` reads an untyped value back at its type.  The typed copies
between storage and memory are `Semantics/Heap.lean`'s; the typed stores,
the recursor forms' `match` twins and `SVal.find_save_same` are
`Semantics/Storage.lean`'s (W10.5.1).
-/

namespace Solidity

open Semantics (structDef lookupBy setBy tyRank fieldsRank structRank)

/-! ## Lists -/

theorem lookupBy_map_snd {κ α β : Type} [DecidableEq κ] (f : α → β) (k : κ) :
    (l : List (κ × α)) →
    lookupBy k (l.map (fun e => (e.1, f e.2))) = (lookupBy k l).map f
  | [] => rfl
  | (k', v) :: rest => by
    simp only [List.map_cons, lookupBy]
    split
    · rfl
    · exact lookupBy_map_snd f k rest

theorem setBy_map_snd {κ α β : Type} [DecidableEq κ] (f : α → β) (k : κ) (x : α) :
    (l : List (κ × α)) →
    setBy k (f x) (l.map (fun e => (e.1, f e.2))) = (setBy k x l).map (fun e => (e.1, f e.2))
  | [] => rfl
  | (k', v) :: rest => by
    simp only [List.map_cons, setBy]
    split
    · rfl
    · simp only [List.map_cons, setBy_map_snd f k x rest]

namespace SList

theorem erase_ofList {E : Ty} (l : List (SVal E)) : (ofList l).erase = l.map SVal.erase := by
  rw [erase_eq, toList_ofList]

theorem length_erase {E : Ty} (l : SList E) : l.erase.length = l.length := by
  rw [erase_eq, List.length_map]; rfl

end SList

theorem SVec.length_erase {E : Ty} {n : Nat} (l : SVec E n) : l.erase.length = n := by
  rw [erase_eq, List.length_map, length_toList]

theorem SVec.erase_ofList {E : Ty} (l : List (SVal E)) : (SVec.ofList l).erase = l.map SVal.erase := by
  rw [erase_eq, toList_ofList]

/-! ## Members -/

namespace SFields

theorem lookupBy_erase {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (st : SFields fs) →
    (h : lookupBy f fs = some T) → lookupBy f st.erase = some (st.get h).erase
  | _, _, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | _, _, @SFields.cons f' T' _ v rest, h => by
    by_cases e : f = f'
    · subst e
      have hT : T' = _ := lookupBy_cons_pos rfl h
      subst hT
      simp only [SFields.erase, get_cons, lookupBy, ↓reduceIte, ↓reduceDIte]
    · simp only [SFields.erase, get_cons, lookupBy, if_neg e, dif_neg e]
      exact lookupBy_erase rest _

theorem set_eq_setM {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (st : SFields fs) →
    (h : lookupBy f fs = some T) → (x : SVal T) → st.set h x = st.setM h x
  | _, _, .nil, _, _ => rfl
  | _, _, @SFields.cons f' T' _ v rest, h, x => by
    rw [set_cons]
    by_cases e : f = f'
    · simp only [e, ↓reduceDIte, setM]
    · simp only [e, ↓reduceDIte, setM, set_eq_setM rest]

theorem setBy_erase {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (st : SFields fs) →
    (h : lookupBy f fs = some T) → (x : SVal T) → setBy f x.erase st.erase = (st.set h x).erase
  | _, _, .nil, h, _ => by simp only [lookupBy, reduceCtorEq] at h
  | _, _, @SFields.cons f' T' _ v rest, h, x => by
    by_cases e : f = f'
    · subst e
      have hT : T' = _ := lookupBy_cons_pos rfl h
      subst hT
      simp only [SFields.erase, set_cons, setBy, ↓reduceIte, ↓reduceDIte]
    · simp only [SFields.erase, set_cons, setBy, if_neg e, dif_neg e]
      exact congrArg _ (setBy_erase rest _ x)

end SFields

/-! ## Find and save -/

/-- A slot taken: the untyped bounds test and the typed `getElem?` agree. -/
theorem slot_erase {E : Ty} {β γ : Type} (L : List (SVal E)) (M : List Semantics.SVal)
    (hM : M = L.map SVal.erase) (i : Int) (f : β → γ) (g : Semantics.SVal → Semantics.Res γ)
    (g' : SVal E → Option β) (hg : ∀ x : SVal E, g x.erase = toRes f (g' x)) :
    (if h : 0 ≤ i ∧ i.toNat < M.length then g (M.get ⟨i.toNat, h.2⟩) else .error .revert) =
      toRes f (if 0 ≤ i then
        match L[i.toNat]? with
        | some x => g' x
        | none => none
      else none) := by
  subst hM
  by_cases hi : 0 ≤ i
  · by_cases hl : i.toNat < L.length
    · rw [dif_pos ⟨hi, by simpa only [List.length_map] using hl⟩, if_pos hi,
        List.getElem?_eq_getElem hl]
      simp only [List.get_eq_getElem, List.getElem_map]
      exact hg _
    · rw [dif_neg (fun h => hl (by simpa only [List.length_map] using h.2)), if_pos hi,
        List.getElem?_eq_none (Nat.le_of_not_lt hl)]
      rfl
  · rw [dif_neg (fun h => hi h.1), if_neg hi]
    rfl

theorem SVal.findM_erase : {T U : Ty} → (v : SVal T) → (p : Path T U) →
    v.erase.find p.erase = toRes SVal.erase (v.findM p)
  | _, _, v, .nil => by cases v <;> with_unfolding_all rfl
  | _, _, .struct fs, .field h p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.find, SFields.lookupBy_erase fs h, findM,
      findM_erase _ p]
  | _, _, .array e sh _, .at i p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.find, findM]
    exact slot_erase _ _ (by rw [SVec.erase_eq, SList.erase_eq, List.map_append]) i _
      (fun w => w.find p.erase) _ (fun x => findM_erase x p)
  | _, _, .fixed e, .atF i p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.find, findM]
    exact slot_erase _ _ (by rw [SVec.erase_eq, List.append_nil]) i _
      (fun w => w.find p.erase) _ (fun x => findM_erase x p)
  | _, _, .map m d, .key k p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.find, findM, SMap.erase_eq,
      lookupBy_map_snd SVal.erase k m.toList]
    cases lookupBy k m.toList with
    | none => exact findM_erase d p
    | some x => exact findM_erase x p

theorem SVal.findLiveM_erase : {T U : Ty} → (v : SVal T) → (p : Path T U) →
    v.erase.findLive p.erase = toRes SVal.erase (v.findLiveM p)
  | _, _, v, .nil => by cases v <;> with_unfolding_all rfl
  | _, _, .struct fs, .field h p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.findLive, SFields.lookupBy_erase fs h,
      findLiveM, findLiveM_erase _ p]
  | _, _, .array e sh _, .at i p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.findLive, findLiveM]
    exact slot_erase _ _ (SVec.erase_eq e) i _ (fun w => w.findLive p.erase) _
      (fun x => findLiveM_erase x p)
  | _, _, .fixed e, .atF i p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.findLive, findLiveM]
    exact slot_erase _ _ (SVec.erase_eq e) i _ (fun w => w.findLive p.erase) _
      (fun x => findLiveM_erase x p)
  | _, _, .map m d, .key k p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.findLive, findLiveM, SMap.erase_eq,
      lookupBy_map_snd SVal.erase k m.toList]
    cases lookupBy k m.toList with
    | none => exact findLiveM_erase d p
    | some x => exact findLiveM_erase x p

theorem SVal.saveM_erase : {T U : Ty} → (v : SVal T) → (p : Path T U) → (new : SVal U) →
    v.erase.save p.erase new.erase = toRes SVal.erase (v.saveM p new)
  | _, _, v, .nil, new => by cases v <;> with_unfolding_all rfl
  | _, _, .struct fs, .field h p, new => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.save, SFields.lookupBy_erase fs h, saveM,
      saveM_erase _ p new]
    cases (fs.get h).saveM p new with
    | none => rfl
    | some x =>
      simp only [toRes, bind, Except.bind, Option.bind, SFields.setBy_erase fs h x]
      with_unfolding_all rfl
  | _, _, .array e sh _, .at i p, new => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.save, saveM]
    refine slot_erase _ (e.erase ++ sh.erase)
      (by rw [SVec.erase_eq, SList.erase_eq, List.map_append]) i _ (fun w => do
        let u ← w.save p.erase new.erase
        let slots := (e.erase ++ sh.erase).set i.toNat u
        .ok (Semantics.SVal.array (slots.take e.erase.length) (slots.drop e.erase.length) false))
      _ (fun x => ?_)
    simp only [saveM_erase x p new]
    cases x.saveM p new with
    | none => rfl
    | some x' =>
      simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SList.erase_eq,
        SList.toList_ofList, SVec.erase_eq, SVec.toList_ofList, SVec.length_toList,
        ← List.map_append, ← List.map_set, ← List.map_take, ← List.map_drop, List.length_map]
  | _, _, .fixed e, .atF i p, new => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.save, saveM]
    refine slot_erase _ (e.erase ++ []) (by rw [SVec.erase_eq, List.append_nil]) i _
      (fun w => do
        let u ← w.save p.erase new.erase
        let slots := (e.erase ++ []).set i.toNat u
        .ok (Semantics.SVal.array (slots.take e.erase.length) (slots.drop e.erase.length) true))
      _ (fun x => ?_)
    simp only [saveM_erase x p new]
    cases x.saveM p new with
    | none => rfl
    | some x' =>
      simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SVec.erase_eq,
        SVec.toList_set, List.append_nil, ← List.map_set, List.length_map]
      have hl : (List.map SVal.erase (e.toList.set i.toNat x')).length ≤ e.toList.length := by
        simp only [List.length_map, List.length_set, Nat.le_refl]
      rw [List.take_of_length_le hl, List.drop_of_length_le hl]
  | _, _, .map m d, .key k p, new => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.save, saveM, SMap.erase_eq,
      lookupBy_map_snd SVal.erase k m.toList]
    cases lookupBy k m.toList with
    | none =>
      simp only [Option.map, saveM_erase d p new]
      cases d.saveM p new with
      | none => rfl
      | some x' =>
        simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SMap.erase_eq,
          SMap.toList_ofList, setBy_map_snd SVal.erase]
    | some x =>
      simp only [Option.map, saveM_erase x p new]
      cases x.saveM p new with
      | none => rfl
      | some x' =>
        simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SMap.erase_eq,
          SMap.toList_ofList, setBy_map_snd SVal.erase]

theorem SVal.find_erase {T U : Ty} (v : SVal T) (p : Path T U) :
    v.erase.find p.erase = toRes SVal.erase (v.find p) := by
  rw [SVal.find_eq_findM]; exact SVal.findM_erase v p

theorem SVal.findLive_erase {T U : Ty} (v : SVal T) (p : Path T U) :
    v.erase.findLive p.erase = toRes SVal.erase (v.findLive p) := by
  rw [SVal.findLive_eq_findLiveM]; exact SVal.findLiveM_erase v p

theorem SVal.save_erase {T U : Ty} (v : SVal T) (p : Path T U) (new : SVal U) :
    v.erase.save p.erase new.erase = toRes SVal.erase (v.save p new) := by
  rw [SVal.save_eq_saveM]; exact SVal.saveM_erase v p new

/-! ## Defaults -/

theorem SFields.dfltBelow_erase (k : Nat) (ih : (T : Ty) → tyRank T < k → SVal T)
    (hih : ∀ T h, (ih T h).erase = Semantics.defaultForTy T) :
    (fs : List (Name × Ty)) → (h : fieldsRank fs < k) →
    (SFields.dfltBelow k ih fs h).erase = Semantics.defaultForFields fs
  | [], _ => by simp only [SFields.dfltBelow, SFields.erase, Semantics.defaultForFields]
  | (f, T) :: fs, h => by
    simp only [SFields.dfltBelow, SFields.erase, Semantics.defaultForFields, hih,
      SFields.dfltBelow_erase k ih hih fs]

theorem SVec.erase_replicate {E : Ty} (v : SVal E) (n : Nat) :
    (SVec.replicate v n).erase = List.replicate n v.erase := by
  rw [erase_eq, toList_replicate, List.map_replicate]

mutual
theorem SVal.dfltAt_erase (k : Nat) (ih : (T : Ty) → tyRank T < k → SVal T)
    (hih : ∀ T h, (ih T h).erase = Semantics.defaultForTy T) :
    (T : Ty) → (h : tyRank T < k + 1) → (SVal.dfltAt k ih T h).erase = Semantics.defaultForTy T
  | .prim .bool, _ | .prim .uint, _ | .prim .int, _ => by
    simp only [SVal.dfltAt, SVal.erase, PrimTy.dflt, PrimTy.erase, Semantics.defaultForTy]
  | .ref R, h => SVal.dfltRefAt_erase k ih hih R h

theorem SVal.dfltRefAt_erase (k : Nat) (ih : (T : Ty) → tyRank T < k → SVal T)
    (hih : ∀ T h, (ih T h).erase = Semantics.defaultForTy T) :
    (R : RefTy) → (h : tyRank (.ref R) < k + 1) →
    (SVal.dfltRefAt k ih R h).erase = Semantics.defaultForTy (.ref R)
  | .struct s, h => by
    simp only [SVal.dfltRefAt, SVal.erase, Semantics.defaultForTy, SFields.dfltBelow_erase k ih hih]
  | .array _, _ => by
    simp only [SVal.dfltRefAt, SVal.erase, SVec.erase, SList.erase, Semantics.defaultForTy]
  | .fixed E n, h => by
    simp only [SVal.dfltRefAt, SVal.erase, Semantics.defaultForTy, SVec.erase_replicate,
      SVal.dfltAt_erase k ih hih E]
  | .mapping _ V, h => by
    simp only [SVal.dfltRefAt, SVal.erase, SMap.erase, Semantics.defaultForTy,
      SVal.dfltAt_erase k ih hih V]
end

theorem SVal.dfltBelow_erase : (k : Nat) → (T : Ty) → (h : tyRank T < k) →
    (SVal.dfltBelow k T h).erase = Semantics.defaultForTy T
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, T, h => SVal.dfltAt_erase k _ (SVal.dfltBelow_erase k) T h

/-- `SVal.dflt` is `defaultForTy`. -/
theorem SVal.dflt_erase (T : Ty) : (SVal.dflt T).erase = Semantics.defaultForTy T :=
  SVal.dfltBelow_erase _ T _

theorem SFields.dflt_erase : (fs : List (Name × Ty)) →
    (SFields.dflt fs).erase = fs.map fun (n, T) => (n, Semantics.defaultForTy T)
  | [] => by with_unfolding_all rfl
  | (f, T) :: fs => by
    simp only [SFields.dflt, SFields.erase, SVal.dflt_erase, SFields.dflt_erase fs, List.map_cons]

/-- A contract starts in the erasure of `Storage.init`. -/
theorem Storage.init_erase (C : Contract) : (Storage.init C).erase = C.initStorage :=
  SFields.dflt_erase C.vars

theorem pushSlot_erase (E : Ty) : (l : List (SVal E)) →
    Semantics.pushSlot E (l.map SVal.erase) =
      ((pushSlot E l).1.erase, (pushSlot E l).2.map SVal.erase)
  | [] => by simp only [List.map_nil, Semantics.pushSlot, pushSlot, SVal.dflt_erase]
  | c :: rest => by
    simp only [List.map_cons, Semantics.pushSlot, pushSlot]
    split <;> simp only [SVal.dflt_erase]

/-! ## Delete, strip -/

theorem defaultOfElems_eq : (l : List Semantics.SVal) →
    Semantics.SVal.defaultOf.defaultOfElems l = l.map Semantics.SVal.defaultOf
  | [] => rfl
  | _ :: rest => congrArg (_ :: ·) (defaultOfElems_eq rest)

theorem stripElems_eq : (l : List Semantics.SVal) →
    Semantics.SVal.strip.stripElems l = l.map Semantics.SVal.strip
  | [] => rfl
  | _ :: rest => congrArg (_ :: ·) (stripElems_eq rest)

mutual
theorem SVal.defaultOf_erase : {T : Ty} → (v : SVal T) → v.defaultOf.erase = v.erase.defaultOf
  | _, @SVal.prim .bool _ | _, @SVal.prim .uint _ | _, @SVal.prim .int _ => by with_unfolding_all rfl
  | _, .struct fs => by
    simp only [SVal.defaultOf, SVal.erase, Semantics.SVal.defaultOf, SFields.defaultOf_erase fs]
  | _, .array e sh _ => by
    simp only [SVal.defaultOf, SVal.erase, Semantics.SVal.defaultOf, SList.erase_ofList,
      List.map_append, ← SVec.erase_eq, ← SList.erase_eq, SVec.defaultOf_erase e, SVec.erase]
  | _, .fixed e => by
    simp only [SVal.defaultOf, SVal.erase, Semantics.SVal.defaultOf, SVec.defaultOf_erase e]
  | _, .map m d => by with_unfolding_all rfl

theorem SFields.defaultOf_erase : {fs : List (Name × Ty)} → (st : SFields fs) →
    (SFields.defaultOf st).erase = Semantics.SVal.defaultOf.defaultOfFields st.erase
  | _, .nil => by with_unfolding_all rfl
  | _, .cons v rest => by
    simp only [SFields.defaultOf, SFields.erase, Semantics.SVal.defaultOf.defaultOfFields,
      SVal.defaultOf_erase v, SFields.defaultOf_erase rest]

theorem SList.defaultOf_erase : {E : Ty} → (l : SList E) →
    (SList.defaultOf l).erase = Semantics.SVal.defaultOf.defaultOfElems l.erase
  | _, .nil => by with_unfolding_all rfl
  | _, .cons v rest => by
    simp only [SList.defaultOf, SList.erase, Semantics.SVal.defaultOf.defaultOfElems,
      SVal.defaultOf_erase v, SList.defaultOf_erase rest]

theorem SVec.defaultOf_erase : {E : Ty} → {n : Nat} → (l : SVec E n) →
    (SVec.defaultOf l).erase = Semantics.SVal.defaultOf.defaultOfElems l.erase
  | _, _, .nil => by with_unfolding_all rfl
  | _, _, .cons v rest => by
    simp only [SVec.defaultOf, SVec.erase, Semantics.SVal.defaultOf.defaultOfElems,
      SVal.defaultOf_erase v, SVec.defaultOf_erase rest]
end

mutual
theorem SVal.strip_erase : {T : Ty} → (v : SVal T) → v.strip.erase = v.erase.strip
  | _, .prim _ => by with_unfolding_all rfl
  | _, .struct fs => by
    simp only [SVal.strip, SVal.erase, Semantics.SVal.strip, SFields.strip_erase fs]
  | _, .array e _ _ => by
    simp only [SVal.strip, SVal.erase, Semantics.SVal.strip, SVec.strip_erase e, SList.erase]
  | _, .fixed e => by
    simp only [SVal.strip, SVal.erase, Semantics.SVal.strip, SVec.strip_erase e]
  | _, .map m d => by with_unfolding_all rfl

theorem SFields.strip_erase : {fs : List (Name × Ty)} → (st : SFields fs) →
    (SFields.strip st).erase = Semantics.SVal.strip.stripFields st.erase
  | _, .nil => by with_unfolding_all rfl
  | _, .cons v rest => by
    simp only [SFields.strip, SFields.erase, Semantics.SVal.strip.stripFields,
      SVal.strip_erase v, SFields.strip_erase rest]

theorem SList.strip_erase : {E : Ty} → (l : SList E) →
    (SList.strip l).erase = Semantics.SVal.strip.stripElems l.erase
  | _, .nil => by with_unfolding_all rfl
  | _, .cons v rest => by
    simp only [SList.strip, SList.erase, Semantics.SVal.strip.stripElems,
      SVal.strip_erase v, SList.strip_erase rest]

theorem SVec.strip_erase : {E : Ty} → {n : Nat} → (l : SVec E n) →
    (SVec.strip l).erase = Semantics.SVal.strip.stripElems l.erase
  | _, _, .nil => by with_unfolding_all rfl
  | _, _, .cons v rest => by
    simp only [SVec.strip, SVec.erase, Semantics.SVal.strip.stripElems,
      SVal.strip_erase v, SVec.strip_erase rest]
end

/-! ## Copy over

A struct is copied member by member, in order (solc); the untyped `overlay`
finds each member of the old value by name.  The two agree because no
struct has two members of one name (`structDef_nodup`). -/

theorem tyRank_le_fieldsRank : {fs : List (Name × Ty)} → {fT : Name × Ty} → fT ∈ fs →
    tyRank fT.2 ≤ fieldsRank fs
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => Nat.le_trans (tyRank_le_fieldsRank h) (Nat.le_max_right _ _)

theorem lookupBy_append_of_none {κ α : Type} [DecidableEq κ] {k : κ} :
    (l₁ l₂ : List (κ × α)) → lookupBy k l₁ = none → lookupBy k (l₁ ++ l₂) = lookupBy k l₂
  | [], _, _ => rfl
  | (k', v) :: rest, l₂, h => by
    simp only [lookupBy] at h
    split at h
    · cases h
    · simp only [List.cons_append, lookupBy, if_neg ‹¬k = k'›]
      exact lookupBy_append_of_none rest l₂ h

mutual
theorem SVal.overlay_erase : {T : Ty} → (o v : SVal T) →
    (o.overlay v).erase = o.erase.overlay v.erase
  | _, .prim _, .prim _ => by with_unfolding_all rfl
  | .ref (.struct s), .struct ofs, .struct nfs => by
    simp only [SVal.overlay, SVal.erase, Semantics.SVal.overlay]
    rw [SFields.overlay_erase [] (fun _ _ _ => rfl) (structDef_nodup s) ofs nfs, List.nil_append]
  | _, .array oel osh _, .array nel _ _ => by
    simp only [SVal.overlay, SVal.erase, Semantics.SVal.overlay, SList.erase_ofList,
      List.map_append, List.map_drop, List.map_map, SVec.length_erase]
    have hd : List.map (SVal.erase ∘ SVal.defaultOf) oel.toList =
        List.map Semantics.SVal.defaultOf oel.erase := by
      rw [SVec.erase_eq, List.map_map]
      congr 1
      funext x
      exact SVal.defaultOf_erase x
    rw [SVec.overlayOn_erase (oel.toList ++ osh.toList) nel, defaultOfElems_eq, hd,
      List.map_append, ← SVec.erase_eq, ← SList.erase_eq, List.map_drop]
  | _, .fixed oel, .fixed nel => by
    simp only [SVal.overlay, SVal.erase, Semantics.SVal.overlay, List.append_nil,
      SVec.overlayOn_erase oel.toList nel, ← SVec.erase_eq, SVec.length_erase, List.drop_nil]
    rw [List.drop_of_length_le (by rw [SVec.length_erase]; exact Nat.le_refl _)]
    rfl
  | _, .map _ _, .map _ _ => by with_unfolding_all rfl

theorem SFields.overlay_erase (pre : List (Name × Semantics.SVal)) :
    {fs : List (Name × Ty)} →
    (∀ k T, lookupBy k fs = some T → lookupBy k pre = none) →
    Semantics.nodupKeysB fs = true → (os ns : SFields fs) →
    (SFields.overlay os ns).erase = Semantics.SVal.overlay.overlayFields (pre ++ os.erase) ns.erase
  | [], _, _, .nil, .nil => by with_unfolding_all rfl
  | (f, T) :: fs, hpre, hk, .cons o os, .cons v ns => by
    simp only [Semantics.nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hk
    have hf0 : lookupBy f (pre ++ (f, o.erase) :: os.erase) = some o.erase := by
      rw [lookupBy_append_of_none _ _ (hpre f T (by simp only [lookupBy, ↓reduceIte]))]
      simp only [lookupBy, ↓reduceIte]
    simp only [SFields.overlay, SFields.erase, Semantics.SVal.overlay.overlayFields, hf0,
      SVal.overlay_erase o v]
    have := SFields.overlay_erase (pre ++ [(f, o.erase)]) (fs := fs)
      (fun k T' h => by
        have hkf : ¬k = f := fun e => by rw [e, hk.1] at h; cases h
        rw [lookupBy_append_of_none _ _ (hpre k T' (by simp only [lookupBy, if_neg hkf]; exact h))]
        simp only [lookupBy, if_neg hkf])
      hk.2 os ns
    rw [this, List.append_assoc]
    rfl

theorem SVec.overlayOn_erase {E : Ty} : {n : Nat} → (L : List (SVal E)) →
    (ns : SVec E n) →
    (SVec.overlayOn L ns).erase =
      Semantics.SVal.overlay.overlayElems (L.map SVal.erase) ns.erase
  | _, [], ns => by
    simp only [SVec.overlayOn_nil_left, List.map_nil, Semantics.SVal.overlay.overlayElems,
      SVec.strip_erase]
  | _, o :: os, .cons v rest => by
    simp only [SVec.overlayOn, SVec.erase, List.map_cons,
      Semantics.SVal.overlay.overlayElems, SVal.overlay_erase o v,
      SVec.overlayOn_erase os rest]
  | _, _ :: _, .nil => by with_unfolding_all rfl
end

/-! ## Storage

Each lemma takes the untyped state `σ` whose storage is the erasure of `st`. -/

namespace Storage

variable {C : Contract} {σ : Semantics.State} {st : Storage C}

/-- `σ` with its storage replaced by the erasure of `st`. -/
def into (σ : Semantics.State) (st : Storage C) : Semantics.State := { σ with storage := st.erase }

theorem findStorage_erase (hs : σ.storage = st.erase) {U : Ty} (r : SRef C U) :
    σ.findStorage r.root r.path.erase = toRes SVal.erase (st.find r) := by
  simp only [Semantics.State.findStorage, hs, Storage.erase, SFields.lookupBy_erase st r.hroot,
    Storage.find]
  exact SVal.find_erase _ _

theorem findLive_erase (hs : σ.storage = st.erase) {U : Ty} (r : SRef C U) :
    σ.findLive r.root r.path.erase = toRes SVal.erase (st.findLive r) := by
  simp only [Semantics.State.findLive, hs, Storage.erase, SFields.lookupBy_erase st r.hroot,
    Storage.findLive]
  exact SVal.findLive_erase _ _

theorem saveStorage_erase (hs : σ.storage = st.erase) {U : Ty} (r : SRef C U) (new : SVal U) :
    σ.saveStorage r.root r.path.erase new.erase = toRes (into σ) (st.save r new) := by
  simp only [Semantics.State.saveStorage, hs, Storage.erase, SFields.lookupBy_erase st r.hroot,
    Storage.save, SVal.save_erase]
  cases (st.get r.hroot).save r.path new with
  | none => rfl
  | some v =>
    simp only [toRes, bind, Except.bind, Option.bind, into, Storage.erase,
      SFields.setBy_erase st r.hroot v]

theorem checkIndex_erase (hs : σ.storage = st.erase) {R : RefTy} {k : PrimTy} {V : Ty}
    (r : SRef C (.ref R)) (it : IndexTy R k V) (i : Int) :
    σ.checkIndex r.root r.path.erase i = toRes id (st.checkIndex r it i) := by
  simp only [Semantics.State.checkIndex, findStorage_erase hs, Storage.checkIndex]
  cases st.find r with
  | none => rfl
  | some v =>
    simp only [toRes, bind, Except.bind, Option.bind]
    cases it with
    | map => cases v; with_unfolding_all rfl
    | arr a =>
      cases a with
      | dyn =>
        cases v with
        | array e sh _ =>
          simp only [SVal.erase, SVec.length_erase, Storage.inBounds, SVal.view_array]
          split <;> rfl
      | fixed =>
        cases v with
        | fixed e =>
          simp only [SVal.erase, SVec.length_erase, Storage.inBounds]
          split <;> rfl

theorem arrayLen_erase (hs : σ.storage = st.erase) {E : Ty} (r : SRef C (.ref (.array E))) :
    arrayLen σ r.root r.path.erase = toRes PrimTy.erase (st.len r) := by
  simp only [arrayLen, findStorage_erase hs, Storage.len]
  cases st.find r with
  | none => rfl
  | some v =>
    cases v with
    | array e sh _ =>
      simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SVec.length_erase]
      rfl

/-- Below the bound in the erasure, the typed array is not full. -/
theorem full_eq_false {E : Ty}
    (hs : σ.storage = st.erase) (r : SRef C (.ref (.array E)))
    (h : ∀ elems sh fx, σ.findStorage r.root r.path.erase = .ok (.array elems sh fx) →
      elems.length + 1 < 2 ^ 256) :
    st.full r = false := by
  unfold Storage.full
  have he := Storage.findStorage_erase hs r
  cases hf : st.find r with
  | none => rfl
  | some v =>
    rw [hf] at he
    cases v with
    | @array _ n e sh hn =>
      have hl := h e.erase sh.erase false (by rw [he]; simp only [toRes, SVal.erase_array])
      rw [SVec.length_erase] at hl
      simp only [SVal.view_array, hl, decide_true, Bool.not_true]

/-- Below the bound, the array is not full. -/
theorem full_false {E : Ty} {r : SRef C (.ref (.array E))} (h : st.full r = false) :
    ∀ v, st.find r = some v → (SVal.view v : ArrView E).n + 1 < 2 ^ 256 := by
  intro v hv
  unfold Storage.full at h
  rw [hv] at h
  simpa only [Bool.not_eq_false', decide_eq_true_eq] using h

theorem pushAt_erase (hs : σ.storage = st.erase) {E : Ty} (r : SRef C (.ref (.array E)))
    (val : Semantics.SVal → Semantics.Res Semantics.SVal) (val' : SVal E → Option (SVal E))
    (hval : ∀ x : SVal E, val x.erase = toRes SVal.erase (val' x))
    (hfull : st.full r = false ∨ ∀ x, val' x = none) :
    pushAt σ E r.root r.path.erase val = toRes (into σ) (st.push r val') := by
  simp only [pushAt, findStorage_erase hs, Storage.push]
  cases hf : st.find r with
  | none => rfl
  | some v =>
    cases v with
    | @array _ n e sh h =>
      simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SList.erase_eq sh,
        pushSlot_erase, hval, SVal.view_array]
      cases hx : val' (pushSlot E sh.toList).1 with
      | none => with_unfolding_all rfl
      | some x =>
        have hb : n + 1 < 2 ^ 256 := by
          rcases hfull with hfull | hnone
          · simpa only [SVal.view_array] using full_false hfull _ hf
          · rw [hnone] at hx; cases hx
        have hnew : Semantics.SVal.array (e.erase ++ [x.erase])
            (List.map SVal.erase (pushSlot E sh.toList).2) false =
            (SVal.array (SVec.ofList (e.toList ++ [x])) (.ofList (pushSlot E sh.toList).2)
              (SVec.snoc_lt_bound e x hb)).erase := by
          simp only [SVal.erase, SVec.erase_eq, SVec.toList_ofList,
            SList.erase_eq, SList.toList_ofList, List.map_append, List.map_cons, List.map_nil]
        simp only [dif_pos hb]
        rw [hnew, saveStorage_erase hs]
        with_unfolding_all rfl

theorem pushPlaceAt_erase (hs : σ.storage = st.erase) {E : Ty} (r : SRef C (.ref (.array E)))
    (hfull : st.full r = false) :
    pushPlaceAt σ E r.root r.path.erase =
      toRes (fun p : Storage C × Nat => (into σ p.1, (p.2 : Int))) (st.pushPlace r) := by
  have hb := full_false hfull
  simp only [pushPlaceAt, findStorage_erase hs, Storage.pushPlace]
  cases hf : st.find r with
  | none => rfl
  | some v =>
    have hb := hb v hf
    cases v with
    | array e sh h =>
      simp only [SVal.view_array] at hb
      have hnew : Semantics.SVal.array (e.erase ++ [(pushSlot E sh.toList).1.erase])
          (List.map SVal.erase (pushSlot E sh.toList).2) false =
          (SVal.array (SVec.ofList (e.toList ++ [(pushSlot E sh.toList).1]))
            (.ofList (pushSlot E sh.toList).2) (SVec.snoc_lt_bound e _ hb)).erase := by
        simp only [SVal.erase, SVec.erase_eq, SVec.toList_ofList,
          SList.erase_eq, SList.toList_ofList, List.map_append, List.map_cons, List.map_nil]
      simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SList.erase_eq sh,
        pushSlot_erase, SVal.view_array, dif_pos hb]
      rw [hnew, saveStorage_erase hs]
      cases st.save r (SVal.array (SVec.ofList (e.toList ++ [(pushSlot E sh.toList).1]))
          (.ofList (pushSlot E sh.toList).2) (SVec.snoc_lt_bound e _ hb)) with
      | none => with_unfolding_all rfl
      | some st' => simp only [toRes, SVec.length_erase]; with_unfolding_all rfl

theorem popAt_erase (hs : σ.storage = st.erase) {E : Ty} (keep : Bool)
    (r : SRef C (.ref (.array E))) :
    popAt σ keep r.root r.path.erase = toRes (into σ) (st.pop keep r) := by
  simp only [popAt, findStorage_erase hs, Storage.pop]
  cases st.find r with
  | none => rfl
  | some v =>
    cases v with
    | array e sh h =>
      simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SVec.erase_eq e,
        ← List.map_reverse, SVal.view_array]
      cases hrev : e.toList.reverse with
      | nil => with_unfolding_all rfl
      | cons last restRev =>
        have hdrop : e.toList.dropLast = restRev.reverse := by
          rw [← List.reverse_reverse e.toList, hrev, List.reverse_cons, List.dropLast_concat]
        have hnew : Semantics.SVal.array (List.map SVal.erase restRev).reverse
            ((if keep then last.erase else last.erase.defaultOf) :: sh.erase) false =
            (SVal.array (SVec.ofList e.toList.dropLast)
              (.ofList ((if keep then last else last.defaultOf) :: sh.toList))
              (SVec.dropLast_lt_bound e h)).erase := by
          simp only [SVal.erase, SVec.erase_ofList, hdrop, SList.erase_eq, SList.toList_ofList,
            List.map_reverse, List.map_cons]
          cases keep <;> simp only [Bool.false_eq_true, ↓reduceIte, SVal.defaultOf_erase]
        simp only [List.map_cons]
        rw [hnew, saveStorage_erase hs]
        with_unfolding_all rfl

/-- `delete b` on storage, as the untyped operations write it: the value found, reset,
saved. -/
theorem delete_erase (hs : σ.storage = st.erase) {T : Ty} (r : SRef C T) :
    (do
      let cur ← σ.findStorage r.root r.path.erase
      σ.saveStorage r.root r.path.erase cur.defaultOf) = toRes (into σ) (st.delete r) := by
  simp only [findStorage_erase hs, Storage.delete]
  cases st.find r with
  | none => rfl
  | some v =>
    simp only [toRes, bind, Except.bind, Option.bind, ← SVal.defaultOf_erase]
    exact saveStorage_erase hs r v.defaultOf

theorem writeStorage_erase (hs : σ.storage = st.erase) {T : Ty}
    (r : SRef C T) (new : SVal T) :
    σ.writeStorage r.root r.path.erase new.erase = toRes (into σ) (st.write r new) := by
  have key : ∀ cur : SVal T, σ.saveStorage r.root r.path.erase (cur.erase.overlay new.erase) =
      toRes (into σ) (st.save r (cur.overlay new)) := fun cur => by
    rw [← SVal.overlay_erase, saveStorage_erase hs]
  cases new with
  | prim v =>
    simp only [Semantics.State.writeStorage, SVal.erase, Storage.write, SVal.isPrim,
      Ty.isPrimitive, ↓reduceIte]
    have h := saveStorage_erase hs r (.prim v)
    rw [SVal.erase_prim] at h
    exact h
  | struct fs | array e sh _ | fixed e | map m d =>
    simp only [Semantics.State.writeStorage, SVal.erase, Storage.write, SVal.isPrim,
      Ty.isPrimitive, Bool.false_eq_true, ↓reduceIte, findStorage_erase hs]
    cases st.find r with
    | none => rfl
    | some cur =>
      have h := key cur
      simp only [SVal.erase] at h
      exact h

end Storage

/-! ## Untyped values read back

An untyped value reads back at its type (`SVal.ofU`) exactly when it has
that type's shape. -/

mutual
/-- An untyped storage value read at a type: `none` where it does not fit. -/
def SVal.ofU : Semantics.SVal → (T : Ty) → Option (SVal T)
  | .prim v, .prim p => (PrimTy.ofValue? p v).map SVal.prim
  | .struct fields, .ref (.struct s) => (SFields.ofU fields (structDef s)).map SVal.struct
  | .array elems shadow false, .ref (.array E) =>
    if h : elems.length < 2 ^ 256 then
      match SVec.ofU elems E elems.length, SList.ofU shadow E with
      | some e, some sh => some (.array e sh h)
      | _, _ => none
    else none
  | .array elems [] true, .ref (.fixed E n) => (SVec.ofU elems E n).map SVal.fixed
  | .map entries dflt, .ref (.mapping _ V) =>
    match SMap.ofU entries V, SVal.ofU dflt V with
    | some m, some d => some (.map m d)
    | _, _ => none
  | _, _ => none

def SFields.ofU : List (Name × Semantics.SVal) → (fs : List (Name × Ty)) → Option (SFields fs)
  | [], [] => some .nil
  | (f, v) :: rest, (f', T) :: fs =>
    if f = f' then
      match SVal.ofU v T, SFields.ofU rest fs with
      | some x, some xs => some (.cons x xs)
      | _, _ => none
    else none
  | _, _ => none

def SList.ofU : List Semantics.SVal → (E : Ty) → Option (SList E)
  | [], _ => some .nil
  | v :: rest, E =>
    match SVal.ofU v E, SList.ofU rest E with
    | some x, some xs => some (.cons x xs)
    | _, _ => none

def SVec.ofU : List Semantics.SVal → (E : Ty) → (n : Nat) → Option (SVec E n)
  | [], _, 0 => some .nil
  | v :: rest, E, n + 1 =>
    match SVal.ofU v E, SVec.ofU rest E n with
    | some x, some xs => some (.cons x xs)
    | _, _ => none
  | _, _, _ => none

def SMap.ofU : List (Int × Semantics.SVal) → (V : Ty) → Option (SMap V)
  | [], _ => some .nil
  | (k, v) :: rest, V =>
    match SVal.ofU v V, SMap.ofU rest V with
    | some x, some xs => some (.cons k x xs)
    | _, _ => none
end

/-- An array is its elements: the length index follows. -/
theorem SVal.array_congr {E : Ty} {n m : Nat} (e : SVec E n) (e' : SVec E m) (sh : SList E)
    (h : n < 2 ^ 256) (h' : m < 2 ^ 256) (hl : e.toList = e'.toList) :
    SVal.array e sh h = SVal.array e' sh h' := by
  have hnm : n = m := by rw [← SVec.length_toList e, hl, SVec.length_toList]
  subst hnm
  rw [SVec.eq_of_toList_eq e e' hl]

mutual
theorem SVal.ofU_erase : {T : Ty} → (v : SVal T) → SVal.ofU v.erase T = some v
  | _, @SVal.prim p v => by
    simp only [SVal.erase, SVal.ofU, PrimTy.ofValue?_erase, Option.map_some]
  | _, .struct fs => by
    simp only [SVal.erase, SVal.ofU, SFields.ofU_erase fs, Option.map_some]
  | _, @SVal.array E n e sh h => by
    -- the vector read back at its own length, however the length is written
    have ih := SVec.ofU_erase e
    have key : ∀ (m : Nat), m = n → ∃ l' : SVec E m, SVec.ofU e.erase E m = some l' ∧
        l'.toList = e.toList := by
      intro m hm
      subst hm
      exact ⟨e, ih, rfl⟩
    obtain ⟨e', he', hl⟩ := key _ (SVec.length_erase e)
    simp only [SVal.erase, SVal.ofU, dif_pos (show e.erase.length < 2 ^ 256 by
      rw [SVec.length_erase]; exact h), he', SList.ofU_erase sh]
    exact congrArg some (SVal.array_congr e' e sh _ h hl)
  | _, .fixed e => by
    simp only [SVal.erase, SVal.ofU, SVec.ofU_erase e, Option.map_some]
  | _, .map m d => by
    simp only [SVal.erase, SVal.ofU, SMap.ofU_erase m, SVal.ofU_erase d]

theorem SFields.ofU_erase : {fs : List (Name × Ty)} → (st : SFields fs) →
    SFields.ofU st.erase fs = some st
  | _, .nil => by with_unfolding_all rfl
  | _, .cons v rest => by
    simp only [SFields.erase, SFields.ofU, ↓reduceIte, SVal.ofU_erase v,
      SFields.ofU_erase rest]

theorem SList.ofU_erase : {E : Ty} → (l : SList E) → SList.ofU l.erase E = some l
  | _, .nil => by with_unfolding_all rfl
  | _, .cons v rest => by
    simp only [SList.erase, SList.ofU, SVal.ofU_erase v, SList.ofU_erase rest]

theorem SVec.ofU_erase : {E : Ty} → {n : Nat} → (l : SVec E n) → SVec.ofU l.erase E n = some l
  | _, _, .nil => by with_unfolding_all rfl
  | _, _, .cons v rest => by
    simp only [SVec.erase, SVec.ofU, SVal.ofU_erase v, SVec.ofU_erase rest]

theorem SMap.ofU_erase : {V : Ty} → (m : SMap V) → SMap.ofU m.erase V = some m
  | _, .nil => by with_unfolding_all rfl
  | _, .cons k v rest => by
    simp only [SMap.erase, SMap.ofU, SVal.ofU_erase v, SMap.ofU_erase rest]
end

/-- Erasure is injective: a typed value is its untyped one. -/
theorem SVal.erase_injective {T : Ty} {v w : SVal T} (h : v.erase = w.erase) : v = w := by
  have := SVal.ofU_erase v
  rw [h, SVal.ofU_erase w] at this
  exact (Option.some.inj this).symm

end Solidity
