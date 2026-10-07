import Solidity.Semantics.Core.Storage

/-!
# Typed storage erases to untyped storage

Every typed storage operation (`Semantics/Core/Storage.lean`) erases to its
untyped namesake in `Semantics.lean`, which is therefore never stuck on an
erased input: each lemma reads `untyped op (erase x) = toRes erase (typed op
x)`, and `toRes` has no `stuck`.  This is the storage half of `run_erase`
(`docs/intrinsic.md`, M4b), the bridge until the typed interpreter replaces
`Stmt.run`.

One copy needs a hypothesis: a struct is copied member by member in order
(solc), and the untyped `overlay` looks each member up by name, which agrees
when a struct's members have distinct names (`TyNodup`; `BadDup` does not).

The copies between storage and memory still go through the untyped heap
(M4c types it): `SVal.copyToMem` is `copyStToM` on the erasure, which is
never stuck on a type without mappings, and `SVal.ofU` reads a copied-back
value at its type.
-/

namespace Solidity.Core

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
      simp only [SFields.erase, get, lookupBy, ↓reduceIte, ↓reduceDIte]
    · simp only [SFields.erase, get, lookupBy, if_neg e, dif_neg e]
      exact lookupBy_erase rest _

theorem setBy_erase {f : Name} : {fs : List (Name × Ty)} → {T : Ty} → (st : SFields fs) →
    (h : lookupBy f fs = some T) → (x : SVal T) → setBy f x.erase st.erase = (st.set h x).erase
  | _, _, .nil, h, _ => by simp only [lookupBy, reduceCtorEq] at h
  | _, _, @SFields.cons f' T' _ v rest, h, x => by
    by_cases e : f = f'
    · subst e
      have hT : T' = _ := lookupBy_cons_pos rfl h
      subst hT
      simp only [SFields.erase, set, setBy, ↓reduceIte, ↓reduceDIte]
    · simp only [SFields.erase, set, setBy, if_neg e, dif_neg e]
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

theorem SVal.find_erase : {T U : Ty} → (v : SVal T) → (p : Path T U) →
    v.erase.find p.erase = toRes SVal.erase (v.find p)
  | _, _, v, .nil => by cases v <;> rfl
  | _, _, .struct fs, .field h p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.find, SFields.lookupBy_erase fs h, find,
      find_erase _ p]
  | _, _, .array e sh, .at i p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.find, find]
    exact slot_erase _ _ (by rw [SList.erase_eq, SList.erase_eq, List.map_append]) i _
      (fun w => w.find p.erase) _ (fun x => find_erase x p)
  | _, _, .fixed e, .atF i p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.find, find]
    exact slot_erase _ _ (by rw [SVec.erase_eq, List.append_nil]) i _
      (fun w => w.find p.erase) _ (fun x => find_erase x p)
  | _, _, .map m d, .key k p => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.find, find, SMap.erase_eq,
      lookupBy_map_snd SVal.erase k m.toList]
    cases lookupBy k m.toList with
    | none => exact find_erase d p
    | some x => exact find_erase x p

theorem SVal.save_erase : {T U : Ty} → (v : SVal T) → (p : Path T U) → (new : SVal U) →
    v.erase.save p.erase new.erase = toRes SVal.erase (v.save p new)
  | _, _, v, .nil, new => by cases v <;> rfl
  | _, _, .struct fs, .field h p, new => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.save, SFields.lookupBy_erase fs h, save,
      save_erase _ p new]
    cases (fs.get h).save p new with
    | none => rfl
    | some x =>
      simp only [toRes, bind, Except.bind, Option.bind, SFields.setBy_erase fs h x]
      rfl
  | _, _, .array e sh, .at i p, new => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.save, save]
    refine slot_erase _ (e.erase ++ sh.erase)
      (by rw [SList.erase_eq, SList.erase_eq, List.map_append]) i _ (fun w => do
        let u ← w.save p.erase new.erase
        let slots := (e.erase ++ sh.erase).set i.toNat u
        .ok (Semantics.SVal.array (slots.take e.erase.length) (slots.drop e.erase.length) false))
      _ (fun x => ?_)
    simp only [save_erase x p new]
    cases x.save p new with
    | none => rfl
    | some x' =>
      simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SList.erase_eq,
        SList.toList_ofList, SList.length, ← List.map_append, ← List.map_set, ← List.map_take,
        ← List.map_drop, List.length_map]
  | _, _, .fixed e, .atF i p, new => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.save, save]
    refine slot_erase _ (e.erase ++ []) (by rw [SVec.erase_eq, List.append_nil]) i _
      (fun w => do
        let u ← w.save p.erase new.erase
        let slots := (e.erase ++ []).set i.toNat u
        .ok (Semantics.SVal.array (slots.take e.erase.length) (slots.drop e.erase.length) true))
      _ (fun x => ?_)
    simp only [save_erase x p new]
    cases x.save p new with
    | none => rfl
    | some x' =>
      simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SVec.erase_eq,
        SVec.toList_set, List.append_nil, ← List.map_set, List.length_map]
      have hl : (List.map SVal.erase (e.toList.set i.toNat x')).length ≤ e.toList.length := by
        simp only [List.length_map, List.length_set, Nat.le_refl]
      rw [List.take_of_length_le hl, List.drop_of_length_le hl]
  | _, _, .map m d, .key k p, new => by
    simp only [SVal.erase, Path.erase, Semantics.SVal.save, save, SMap.erase_eq,
      lookupBy_map_snd SVal.erase k m.toList]
    cases lookupBy k m.toList with
    | none =>
      simp only [Option.map, save_erase d p new]
      cases d.save p new with
      | none => rfl
      | some x' =>
        simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SMap.erase_eq,
          SMap.toList_ofList, setBy_map_snd SVal.erase]
    | some x =>
      simp only [Option.map, save_erase x p new]
      cases x.save p new with
      | none => rfl
      | some x' =>
        simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SMap.erase_eq,
          SMap.toList_ofList, setBy_map_snd SVal.erase]

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
    simp only [SVal.dfltRefAt, SVal.erase, SList.erase, Semantics.defaultForTy]
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
  | _, @SVal.prim .bool _ | _, @SVal.prim .uint _ | _, @SVal.prim .int _ => rfl
  | _, .struct fs => by
    simp only [SVal.defaultOf, SVal.erase, Semantics.SVal.defaultOf, SFields.defaultOf_erase fs]
  | _, .array e sh => by
    simp only [SVal.defaultOf, SVal.erase, Semantics.SVal.defaultOf, SList.erase_ofList,
      List.map_append, ← SList.erase_eq, SList.defaultOf_erase e, SList.erase]
  | _, .fixed e => by
    simp only [SVal.defaultOf, SVal.erase, Semantics.SVal.defaultOf, SVec.defaultOf_erase e]
  | _, .map m d => rfl

theorem SFields.defaultOf_erase : {fs : List (Name × Ty)} → (st : SFields fs) →
    (SFields.defaultOf st).erase = Semantics.SVal.defaultOf.defaultOfFields st.erase
  | _, .nil => rfl
  | _, .cons v rest => by
    simp only [SFields.defaultOf, SFields.erase, Semantics.SVal.defaultOf.defaultOfFields,
      SVal.defaultOf_erase v, SFields.defaultOf_erase rest]

theorem SList.defaultOf_erase : {E : Ty} → (l : SList E) →
    (SList.defaultOf l).erase = Semantics.SVal.defaultOf.defaultOfElems l.erase
  | _, .nil => rfl
  | _, .cons v rest => by
    simp only [SList.defaultOf, SList.erase, Semantics.SVal.defaultOf.defaultOfElems,
      SVal.defaultOf_erase v, SList.defaultOf_erase rest]

theorem SVec.defaultOf_erase : {E : Ty} → {n : Nat} → (l : SVec E n) →
    (SVec.defaultOf l).erase = Semantics.SVal.defaultOf.defaultOfElems l.erase
  | _, _, .nil => rfl
  | _, _, .cons v rest => by
    simp only [SVec.defaultOf, SVec.erase, Semantics.SVal.defaultOf.defaultOfElems,
      SVal.defaultOf_erase v, SVec.defaultOf_erase rest]
end

mutual
theorem SVal.strip_erase : {T : Ty} → (v : SVal T) → v.strip.erase = v.erase.strip
  | _, .prim _ => rfl
  | _, .struct fs => by
    simp only [SVal.strip, SVal.erase, Semantics.SVal.strip, SFields.strip_erase fs]
  | _, .array e _ => by
    simp only [SVal.strip, SVal.erase, Semantics.SVal.strip, SList.strip_erase e, SList.erase]
  | _, .fixed e => by
    simp only [SVal.strip, SVal.erase, Semantics.SVal.strip, SVec.strip_erase e]
  | _, .map m d => rfl

theorem SFields.strip_erase : {fs : List (Name × Ty)} → (st : SFields fs) →
    (SFields.strip st).erase = Semantics.SVal.strip.stripFields st.erase
  | _, .nil => rfl
  | _, .cons v rest => by
    simp only [SFields.strip, SFields.erase, Semantics.SVal.strip.stripFields,
      SVal.strip_erase v, SFields.strip_erase rest]

theorem SList.strip_erase : {E : Ty} → (l : SList E) →
    (SList.strip l).erase = Semantics.SVal.strip.stripElems l.erase
  | _, .nil => rfl
  | _, .cons v rest => by
    simp only [SList.strip, SList.erase, Semantics.SVal.strip.stripElems,
      SVal.strip_erase v, SList.strip_erase rest]

theorem SVec.strip_erase : {E : Ty} → {n : Nat} → (l : SVec E n) →
    (SVec.strip l).erase = Semantics.SVal.strip.stripElems l.erase
  | _, _, .nil => rfl
  | _, _, .cons v rest => by
    simp only [SVec.strip, SVec.erase, Semantics.SVal.strip.stripElems,
      SVal.strip_erase v, SVec.strip_erase rest]
end

/-! ## Copy over

A struct is copied member by member, in order (solc); the untyped `overlay`
finds each member of the old value by name.  The two agree when no struct
the type reaches has two members of one name. -/

/-- No struct `T` reaches has two members of one name. -/
inductive TyNodup : Ty → Prop where
  | prim {p : PrimTy} : TyNodup (.prim p)
  | struct {s : Name} (hk : Semantics.nodupKeysB (structDef s) = true)
      (hf : ∀ fT ∈ structDef s, TyNodup fT.2) : TyNodup (.ref (.struct s))
  | array {E : Ty} (h : TyNodup E) : TyNodup (.ref (.array E))
  | fixed {E : Ty} {n : Nat} (h : TyNodup E) : TyNodup (.ref (.fixed E n))
  | mapping {K V : Ty} : TyNodup (.ref (.mapping K V))

theorem lookupBy_append_of_none {κ α : Type} [DecidableEq κ] {k : κ} :
    (l₁ l₂ : List (κ × α)) → lookupBy k l₁ = none → lookupBy k (l₁ ++ l₂) = lookupBy k l₂
  | [], _, _ => rfl
  | (k', v) :: rest, l₂, h => by
    simp only [lookupBy] at h
    split at h
    · cases h
    · simp only [List.cons_append, lookupBy, if_neg ‹¬k = k'›]
      exact lookupBy_append_of_none rest l₂ h

theorem overlayElems_eq_zip : (os vs : List Semantics.SVal) → os.length = vs.length →
    Semantics.SVal.overlay.overlayElems os vs = List.zipWith Semantics.SVal.overlay os vs
  | [], [], _ => rfl
  | _ :: os, _ :: vs, h => congrArg (_ :: ·) (overlayElems_eq_zip os vs (Nat.succ.inj h))

mutual
theorem SVal.overlay_erase : {T : Ty} → TyNodup T → (o v : SVal T) →
    (o.overlay v).erase = o.erase.overlay v.erase
  | _, _, .prim _, .prim _ => rfl
  | _, .struct hk hf, .struct ofs, .struct nfs => by
    simp only [SVal.overlay, SVal.erase, Semantics.SVal.overlay]
    rw [SFields.overlay_erase [] (fun _ _ _ => rfl) hk hf ofs nfs, List.nil_append]
  | _, .array hE, .array oel osh, .array nel _ => by
    simp only [SVal.overlay, SVal.erase, Semantics.SVal.overlay, SList.erase_ofList,
      List.map_append, List.map_drop, List.map_map, SList.length_erase]
    have hd : List.map (SVal.erase ∘ SVal.defaultOf) oel.toList =
        List.map Semantics.SVal.defaultOf oel.erase := by
      rw [SList.erase_eq, List.map_map]
      congr 1
      funext x
      exact SVal.defaultOf_erase x
    rw [SList.overlayOn_erase hE (oel.toList ++ osh.toList) nel, defaultOfElems_eq, hd,
      List.map_append, ← SList.erase_eq, ← SList.erase_eq, List.map_drop]
  | _, .fixed hE, .fixed oel, .fixed nel => by
    simp only [SVal.overlay, SVal.erase, Semantics.SVal.overlay, List.append_nil,
      SVec.overlay_erase hE oel nel, SVec.length_erase, List.drop_nil]
    rw [overlayElems_eq_zip _ _ (by rw [SVec.length_erase, SVec.length_erase]),
      List.drop_of_length_le (by rw [SVec.length_erase]; exact Nat.le_refl _)]
    rfl
  | _, _, .map _ _, .map _ _ => rfl

theorem SFields.overlay_erase (pre : List (Name × Semantics.SVal)) :
    {fs : List (Name × Ty)} →
    (∀ k T, lookupBy k fs = some T → lookupBy k pre = none) →
    Semantics.nodupKeysB fs = true → (∀ fT ∈ fs, TyNodup fT.2) → (os ns : SFields fs) →
    (SFields.overlay os ns).erase = Semantics.SVal.overlay.overlayFields (pre ++ os.erase) ns.erase
  | [], _, _, _, .nil, .nil => rfl
  | (f, T) :: fs, hpre, hk, hf, .cons o os, .cons v ns => by
    simp only [Semantics.nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hk
    have hf0 : lookupBy f (pre ++ (f, o.erase) :: os.erase) = some o.erase := by
      rw [lookupBy_append_of_none _ _ (hpre f T (by simp only [lookupBy, ↓reduceIte]))]
      simp only [lookupBy, ↓reduceIte]
    simp only [SFields.overlay, SFields.erase, Semantics.SVal.overlay.overlayFields, hf0,
      SVal.overlay_erase (hf (f, T) List.mem_cons_self) o v]
    have := SFields.overlay_erase (pre ++ [(f, o.erase)]) (fs := fs)
      (fun k T' h => by
        have hkf : ¬k = f := fun e => by rw [e, hk.1] at h; cases h
        rw [lookupBy_append_of_none _ _ (hpre k T' (by simp only [lookupBy, if_neg hkf]; exact h))]
        simp only [lookupBy, if_neg hkf])
      hk.2 (fun fT h => hf fT (List.mem_cons_of_mem _ h)) os ns
    rw [this, List.append_assoc]
    rfl

theorem SList.overlayOn_erase {E : Ty} (hE : TyNodup E) : (L : List (SVal E)) → (ns : SList E) →
    (SList.overlayOn L ns).erase =
      Semantics.SVal.overlay.overlayElems (L.map SVal.erase) ns.erase
  | [], ns => by
    simp only [SList.overlayOn, List.map_nil, Semantics.SVal.overlay.overlayElems,
      SList.strip_erase]
  | o :: os, .cons v rest => by
    simp only [SList.overlayOn, SList.erase, List.map_cons,
      Semantics.SVal.overlay.overlayElems, SVal.overlay_erase hE o v,
      SList.overlayOn_erase hE os rest]
  | _ :: _, .nil => rfl

theorem SVec.overlay_erase {E : Ty} (hE : TyNodup E) : {n : Nat} → (os ns : SVec E n) →
    (SVec.overlay os ns).erase = List.zipWith Semantics.SVal.overlay os.erase ns.erase
  | _, .nil, .nil => rfl
  | _, .cons o os, .cons v ns => by
    simp only [SVec.overlay, SVec.erase, List.zipWith_cons_cons, SVal.overlay_erase hE o v,
      SVec.overlay_erase hE os ns]
end

end Solidity.Core
