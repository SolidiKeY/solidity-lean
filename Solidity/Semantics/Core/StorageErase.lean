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
    | map => cases v; rfl
    | arr a =>
      cases a with
      | dyn =>
        cases v with
        | array e sh =>
          simp only [SVal.erase, SList.length_erase]
          split <;> rfl
      | fixed =>
        cases v with
        | fixed e =>
          simp only [SVal.erase, SVec.length_erase]
          split <;> rfl

theorem arrayLen_erase (hs : σ.storage = st.erase) {E : Ty} (r : SRef C (.ref (.array E))) :
    arrayLen σ r.root r.path.erase = toRes (fun n : Nat => Semantics.Value.int n) (st.len r) := by
  simp only [arrayLen, findStorage_erase hs, Storage.len]
  cases st.find r with
  | none => rfl
  | some v =>
    cases v with
    | array e sh => simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SList.length_erase]; rfl

theorem pushAt_erase (hs : σ.storage = st.erase) {E : Ty} (r : SRef C (.ref (.array E)))
    (val : Semantics.SVal → Semantics.Res Semantics.SVal) (val' : SVal E → Option (SVal E))
    (hval : ∀ x : SVal E, val x.erase = toRes SVal.erase (val' x)) :
    pushAt σ E r.root r.path.erase val = toRes (into σ) (st.push r val') := by
  simp only [pushAt, findStorage_erase hs, Storage.push]
  cases st.find r with
  | none => rfl
  | some v =>
    cases v with
    | array e sh =>
      simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SList.erase_eq sh,
        pushSlot_erase, hval]
      cases val' (pushSlot E sh.toList).1 with
      | none => rfl
      | some x =>
        have hnew : Semantics.SVal.array (e.erase ++ [x.erase])
            (List.map SVal.erase (pushSlot E sh.toList).2) false =
            (SVal.array (.ofList (e.toList ++ [x])) (.ofList (pushSlot E sh.toList).2)).erase := by
          simp only [SVal.erase, SList.erase_eq, SList.toList_ofList, List.map_append,
            List.map_cons, List.map_nil]
        simp only []
        rw [hnew, saveStorage_erase hs]
        rfl

theorem pushPlaceAt_erase (hs : σ.storage = st.erase) {E : Ty} (r : SRef C (.ref (.array E))) :
    pushPlaceAt σ E r.root r.path.erase =
      toRes (fun p : Storage C × Nat => (into σ p.1, (p.2 : Int))) (st.pushPlace r) := by
  simp only [pushPlaceAt, findStorage_erase hs, Storage.pushPlace]
  cases st.find r with
  | none => rfl
  | some v =>
    cases v with
    | array e sh =>
      have hnew : Semantics.SVal.array (e.erase ++ [(pushSlot E sh.toList).1.erase])
          (List.map SVal.erase (pushSlot E sh.toList).2) false =
          (SVal.array (.ofList (e.toList ++ [(pushSlot E sh.toList).1]))
            (.ofList (pushSlot E sh.toList).2)).erase := by
        simp only [SVal.erase, SList.erase_eq, SList.toList_ofList, List.map_append,
          List.map_cons, List.map_nil]
      simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SList.erase_eq sh,
        pushSlot_erase]
      rw [hnew, saveStorage_erase hs]
      cases st.save r (SVal.array (.ofList (e.toList ++ [(pushSlot E sh.toList).1]))
          (.ofList (pushSlot E sh.toList).2)) with
      | none => rfl
      | some st' => simp only [toRes, SList.length_erase]; rfl

theorem popAt_erase (hs : σ.storage = st.erase) {E : Ty} (keep : Bool)
    (r : SRef C (.ref (.array E))) :
    popAt σ keep r.root r.path.erase = toRes (into σ) (st.pop keep r) := by
  simp only [popAt, findStorage_erase hs, Storage.pop]
  cases st.find r with
  | none => rfl
  | some v =>
    cases v with
    | array e sh =>
      simp only [toRes, bind, Except.bind, Option.bind, SVal.erase, SList.erase_eq e,
        ← List.map_reverse]
      cases e.toList.reverse with
      | nil => rfl
      | cons last restRev =>
        have hnew : Semantics.SVal.array (List.map SVal.erase restRev).reverse
            ((if keep then last.erase else last.erase.defaultOf) :: sh.erase) false =
            (SVal.array (.ofList restRev.reverse)
              (.ofList ((if keep then last else last.defaultOf) :: sh.toList))).erase := by
          simp only [SVal.erase, SList.erase_eq, SList.toList_ofList, List.map_reverse,
            List.map_cons]
          cases keep <;> simp only [Bool.false_eq_true, ↓reduceIte, SVal.defaultOf_erase]
        simp only [List.map_cons]
        rw [hnew, saveStorage_erase hs]
        rfl

/-- `delete b` on storage, as `Stmt.run` writes it: the value found, reset,
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

theorem writeStorage_erase (hs : σ.storage = st.erase) {T : Ty} (hT : TyNodup T)
    (r : SRef C T) (new : SVal T) :
    σ.writeStorage r.root r.path.erase new.erase = toRes (into σ) (st.write r new) := by
  have key : ∀ cur : SVal T, σ.saveStorage r.root r.path.erase (cur.erase.overlay new.erase) =
      toRes (into σ) (st.save r (cur.overlay new)) := fun cur => by
    rw [← SVal.overlay_erase hT, saveStorage_erase hs]
  cases new with
  | prim v => exact saveStorage_erase hs r (.prim v)
  | struct fs | array e sh | fixed e | map m d =>
    simp only [Semantics.State.writeStorage, SVal.erase, Storage.write, SVal.isPrim,
      Bool.false_eq_true, ↓reduceIte, findStorage_erase hs]
    cases st.find r with
    | none => rfl
    | some cur => exact key cur

end Storage

/-! ## Copies through the untyped heap

Until the heap is typed (M4c), a copy between storage and memory goes through
the untyped one: storage to memory copies the erasure, which is never stuck
on a type without mappings, and memory to storage reads the copied value
back at its type (`SVal.ofU`), which can fail only on a heap that does not
fit the type. -/

theorem mapFree_structDef : ∀ s ∈ mapFreeStructs, ∀ fT ∈ structDef s, fT.2.mapFree = true := by
  decide

mutual
theorem SVal.copyStToM_ok : {T : Ty} → (v : SVal T) → T.mapFree = true →
    ∀ s : Semantics.State, ∃ r, Semantics.copyStToM s v.erase = .ok r
  | _, @SVal.prim .bool b, _, s => ⟨_, rfl⟩
  | _, @SVal.prim .uint n, _, s => ⟨_, rfl⟩
  | _, @SVal.prim .int n, _, s => ⟨_, rfl⟩
  | _, @SVal.struct sn fs, h, s => by
    obtain ⟨⟨s', mf⟩, hr⟩ := SFields.copyStFields_ok fs
      (mapFree_structDef sn (by simpa only [Ty.mapFree, decide_eq_true_eq] using h)) s
    exact ⟨_, by simp only [SVal.erase, Semantics.copyStToM, hr]; rfl⟩
  | _, .array e _, h, s => by
    obtain ⟨⟨s', me⟩, hr⟩ := SList.copyStElems_ok e (by simpa only [Ty.mapFree] using h) s
    exact ⟨_, by simp only [SVal.erase, Semantics.copyStToM, hr]; rfl⟩
  | _, .fixed e, h, s => by
    obtain ⟨⟨s', me⟩, hr⟩ := SVec.copyStElems_ok e (by simpa only [Ty.mapFree] using h) s
    exact ⟨_, by simp only [SVal.erase, Semantics.copyStToM, hr]; rfl⟩
  | _, .map _ _, h, _ => by simp only [Ty.mapFree, Bool.false_eq_true] at h

theorem SFields.copyStFields_ok : {fs : List (Name × Ty)} → (st : SFields fs) →
    (∀ fT ∈ fs, fT.2.mapFree = true) →
    ∀ s : Semantics.State, ∃ r, Semantics.copyStFields s st.erase = .ok r
  | _, .nil, _, s => ⟨_, rfl⟩
  | _, .cons v rest, h, s => by
    obtain ⟨⟨s₁, mv⟩, h₁⟩ := SVal.copyStToM_ok v (h _ List.mem_cons_self) s
    obtain ⟨⟨s₂, mr⟩, h₂⟩ := SFields.copyStFields_ok rest
      (fun fT hm => h fT (List.mem_cons_of_mem _ hm)) s₁
    exact ⟨_, by simp only [SFields.erase, Semantics.copyStFields, h₁, bind, Except.bind, h₂]; rfl⟩

theorem SList.copyStElems_ok : {E : Ty} → (l : SList E) → E.mapFree = true →
    ∀ s : Semantics.State, ∃ r, Semantics.copyStElems s l.erase = .ok r
  | _, .nil, _, s => ⟨_, rfl⟩
  | _, .cons v rest, h, s => by
    obtain ⟨⟨s₁, mv⟩, h₁⟩ := SVal.copyStToM_ok v h s
    obtain ⟨⟨s₂, mr⟩, h₂⟩ := SList.copyStElems_ok rest h s₁
    exact ⟨_, by simp only [SList.erase, Semantics.copyStElems, h₁, bind, Except.bind, h₂]; rfl⟩

theorem SVec.copyStElems_ok : {E : Ty} → {n : Nat} → (l : SVec E n) → E.mapFree = true →
    ∀ s : Semantics.State, ∃ r, Semantics.copyStElems s l.erase = .ok r
  | _, _, .nil, _, s => ⟨_, rfl⟩
  | _, _, .cons v rest, h, s => by
    obtain ⟨⟨s₁, mv⟩, h₁⟩ := SVal.copyStToM_ok v h s
    obtain ⟨⟨s₂, mr⟩, h₂⟩ := SVec.copyStElems_ok rest h s₁
    exact ⟨_, by simp only [SVec.erase, Semantics.copyStElems, h₁, bind, Except.bind, h₂]; rfl⟩
end

/-- A storage value copied into fresh memory objects (`copySt`): never stuck
on a type without mappings. -/
def SVal.copyToMem (s : Semantics.State) {T : Ty} (v : SVal T) (h : T.mapFree = true) :
    Semantics.State × Semantics.MVal :=
  match hc : Semantics.copyStToM s v.erase with
  | .ok r => r
  | .error _ => absurd hc (by
      obtain ⟨r, hr⟩ := v.copyStToM_ok h s
      rw [hr]
      exact Except.noConfusion)

theorem SVal.copyStToM_erase (s : Semantics.State) {T : Ty} (v : SVal T) (h : T.mapFree = true) :
    Semantics.copyStToM s v.erase = .ok (v.copyToMem s h) := by
  obtain ⟨r, hr⟩ := v.copyStToM_ok h s
  unfold SVal.copyToMem
  split
  · rename_i r' hc; exact hc
  · rename_i hc; rw [hr] at hc; cases hc

mutual
/-- An untyped storage value read at a type: `none` where it does not fit. -/
def SVal.ofU : Semantics.SVal → (T : Ty) → Option (SVal T)
  | .prim v, .prim p => (PrimTy.ofValue? p v).map SVal.prim
  | .struct fields, .ref (.struct s) => (SFields.ofU fields (structDef s)).map SVal.struct
  | .array elems shadow false, .ref (.array E) =>
    match SList.ofU elems E, SList.ofU shadow E with
    | some e, some sh => some (.array e sh)
    | _, _ => none
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

mutual
theorem SVal.ofU_erase : {T : Ty} → (v : SVal T) → SVal.ofU v.erase T = some v
  | _, @SVal.prim p v => by
    simp only [SVal.erase, SVal.ofU, PrimTy.ofValue?_erase, Option.map_some]
  | _, .struct fs => by
    simp only [SVal.erase, SVal.ofU, SFields.ofU_erase fs, Option.map_some]
  | _, .array e sh => by
    simp only [SVal.erase, SVal.ofU, SList.ofU_erase e, SList.ofU_erase sh]
  | _, .fixed e => by
    simp only [SVal.erase, SVal.ofU, SVec.ofU_erase e, Option.map_some]
  | _, .map m d => by
    simp only [SVal.erase, SVal.ofU, SMap.ofU_erase m, SVal.ofU_erase d]

theorem SFields.ofU_erase : {fs : List (Name × Ty)} → (st : SFields fs) →
    SFields.ofU st.erase fs = some st
  | _, .nil => rfl
  | _, .cons v rest => by
    simp only [SFields.erase, SFields.ofU, ↓reduceIte, SVal.ofU_erase v,
      SFields.ofU_erase rest]

theorem SList.ofU_erase : {E : Ty} → (l : SList E) → SList.ofU l.erase E = some l
  | _, .nil => rfl
  | _, .cons v rest => by
    simp only [SList.erase, SList.ofU, SVal.ofU_erase v, SList.ofU_erase rest]

theorem SVec.ofU_erase : {E : Ty} → {n : Nat} → (l : SVec E n) → SVec.ofU l.erase E n = some l
  | _, _, .nil => rfl
  | _, _, .cons v rest => by
    simp only [SVec.erase, SVec.ofU, SVal.ofU_erase v, SVec.ofU_erase rest]

theorem SMap.ofU_erase : {V : Ty} → (m : SMap V) → SMap.ofU m.erase V = some m
  | _, .nil => rfl
  | _, .cons k v rest => by
    simp only [SMap.erase, SMap.ofU, SVal.ofU_erase v, SMap.ofU_erase rest]
end

/-- Erasure is injective: a typed value is its untyped one. -/
theorem SVal.erase_injective {T : Ty} {v w : SVal T} (h : v.erase = w.erase) : v = w := by
  have := SVal.ofU_erase v
  rw [h, SVal.ofU_erase w] at this
  exact (Option.some.inj this).symm

mutual
theorem SVal.erase_of_ofU : (w : Semantics.SVal) → {T : Ty} → {v : SVal T} →
    SVal.ofU w T = some v → v.erase = w
  | .prim pv, T, v, h => by
    cases T with
    | prim p =>
      simp only [SVal.ofU, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [SVal.erase, PrimTy.erase_of_ofValue? hx]
    | ref R => cases R <;> simp only [SVal.ofU, reduceCtorEq] at h
  | .struct fields, T, v, h => by
    cases T with
    | prim p => simp only [SVal.ofU, reduceCtorEq] at h
    | ref R =>
      cases R with
      | struct s =>
        simp only [SVal.ofU, Option.map_eq_some_iff] at h
        obtain ⟨x, hx, rfl⟩ := h
        simp only [SVal.erase, SFields.erase_of_ofU fields hx]
      | array _ | fixed _ _ | mapping _ _ => simp only [SVal.ofU, reduceCtorEq] at h
  | .array elems shadow fx, T, v, h => by
    cases T with
    | prim p => simp only [SVal.ofU, reduceCtorEq] at h
    | ref R =>
      cases R with
      | array E =>
        cases fx with
        | true => simp only [SVal.ofU, reduceCtorEq] at h
        | false =>
          simp only [SVal.ofU] at h
          split at h
          · rename_i e sh he hsh
            cases h
            simp only [SVal.erase, SList.erase_of_ofU elems he, SList.erase_of_ofU shadow hsh]
          · cases h
      | fixed E n =>
        cases fx with
        | false => simp only [SVal.ofU, reduceCtorEq] at h
        | true =>
          cases shadow with
          | cons _ _ => simp only [SVal.ofU, reduceCtorEq] at h
          | nil =>
            simp only [SVal.ofU, Option.map_eq_some_iff] at h
            obtain ⟨x, hx, rfl⟩ := h
            simp only [SVal.erase, SVec.erase_of_ofU elems hx]
      | struct _ | mapping _ _ => simp only [SVal.ofU, reduceCtorEq] at h
  | .map entries dflt, T, v, h => by
    cases T with
    | prim p => simp only [SVal.ofU, reduceCtorEq] at h
    | ref R =>
      cases R with
      | mapping K V =>
        simp only [SVal.ofU] at h
        split at h
        · rename_i m d hm hd
          cases h
          simp only [SVal.erase, SMap.erase_of_ofU entries hm, SVal.erase_of_ofU dflt hd]
        · cases h
      | struct _ | array _ | fixed _ _ => simp only [SVal.ofU, reduceCtorEq] at h

theorem SFields.erase_of_ofU : (l : List (Name × Semantics.SVal)) → {fs : List (Name × Ty)} →
    {st : SFields fs} → SFields.ofU l fs = some st → st.erase = l
  | [], fs, st, h => by
    cases fs with
    | nil => simp only [SFields.ofU, Option.some.injEq] at h; subst h; rfl
    | cons _ _ => simp only [SFields.ofU, reduceCtorEq] at h
  | (f, w) :: rest, fs, st, h => by
    cases fs with
    | nil => simp only [SFields.ofU, reduceCtorEq] at h
    | cons fT fs =>
      obtain ⟨f', T⟩ := fT
      simp only [SFields.ofU] at h
      split at h
      · rename_i e
        subst e
        split at h
        · rename_i x xs hx hxs
          cases h
          simp only [SFields.erase, SVal.erase_of_ofU w hx, SFields.erase_of_ofU rest hxs]
        · cases h
      · cases h

theorem SList.erase_of_ofU : (l : List Semantics.SVal) → {E : Ty} → {xs : SList E} →
    SList.ofU l E = some xs → xs.erase = l
  | [], E, xs, h => by simp only [SList.ofU, Option.some.injEq] at h; subst h; rfl
  | w :: rest, E, xs, h => by
    simp only [SList.ofU] at h
    split at h
    · rename_i x ys hx hys
      cases h
      simp only [SList.erase, SVal.erase_of_ofU w hx, SList.erase_of_ofU rest hys]
    · cases h

theorem SVec.erase_of_ofU : (l : List Semantics.SVal) → {E : Ty} → {n : Nat} → {xs : SVec E n} →
    SVec.ofU l E n = some xs → xs.erase = l
  | [], E, n, xs, h => by
    cases n with
    | zero => simp only [SVec.ofU, Option.some.injEq] at h; subst h; rfl
    | succ n => simp only [SVec.ofU, reduceCtorEq] at h
  | w :: rest, E, n, xs, h => by
    cases n with
    | zero => simp only [SVec.ofU, reduceCtorEq] at h
    | succ n =>
      simp only [SVec.ofU] at h
      split at h
      · rename_i x ys hx hys
        cases h
        simp only [SVec.erase, SVal.erase_of_ofU w hx, SVec.erase_of_ofU rest hys]
      · cases h

theorem SMap.erase_of_ofU : (l : List (Int × Semantics.SVal)) → {V : Ty} → {m : SMap V} →
    SMap.ofU l V = some m → m.erase = l
  | [], V, m, h => by simp only [SMap.ofU, Option.some.injEq] at h; subst h; rfl
  | (k, w) :: rest, V, m, h => by
    simp only [SMap.ofU] at h
    split at h
    · rename_i x ys hx hys
      cases h
      simp only [SMap.erase, SVal.erase_of_ofU w hx, SMap.erase_of_ofU rest hys]
    · cases h
end

/-- A memory value copied to storage (`copyMem`) and read at its type: stuck
only where the untyped heap does not fit `T` (M4c types the heap). -/
def SVal.copyFromMem (s : Semantics.State) (mv : Semantics.MVal) (T : Ty) :
    Semantics.Res (SVal T) := do
  let w ← Semantics.copyMem s mv
  match SVal.ofU w T with
  | some v => pure v
  | none => .error .stuck

theorem SVal.copyMem_erase {s : Semantics.State} {mv : Semantics.MVal} {T : Ty} {v : SVal T}
    (h : SVal.copyFromMem s mv T = .ok v) : Semantics.copyMem s mv = .ok v.erase := by
  unfold SVal.copyFromMem at h
  cases hc : Semantics.copyMem s mv with
  | error e => rw [hc] at h; cases h
  | ok w =>
    rw [hc] at h
    simp only [bind, Except.bind] at h
    split at h
    · rename_i x hx
      cases h
      rw [SVal.erase_of_ofU w hx]
    · cases h

end Solidity.Core
