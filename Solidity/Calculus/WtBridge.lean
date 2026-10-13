import Solidity.Typing.CanonTest
import Solidity.Semantics.StorageErase
import Solidity.Semantics.WellFormed

/-!
# `wt(storage)` on the typed storage

The term `wt(storage)` (`Op1.wt`, `Signature.lean`) still runs the untyped
test on the storage's erasure (`Storage.wtT`: `storageWtB`,
`Semantics/WellFormed.lean`), which the kernel evaluates in certificates.
This module is the bridge to the typed test the reachability theorems are
about (`Storage.wtB`, `Typing/CanonTest.lean`): on the erasure the two agree
(`storageWtB_erase`), for a contract that declares no root twice, test for
test (`SVal.erase_canonB`, `SVal.erase_tightB` on a canonical value,
`SVal.erase_wordsB`).  It is the one reader of the erasure on the
obligations' side, and goes when `Storage.wtT` is the typed test itself
(W10.5.6).
-/

namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB storageWtB storageShapeB storageWordsB)
open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB)
open Semantics.SVal.tightB (tightFieldsB tightElemsB tightEntriesB)
open Semantics.SVal.wordsB (wordsFieldsB wordsElemsB wordsEntriesB)

variable {C : Contract}

theorem SFields.erase_names : {fs : List (Name × Ty)} → (x : SFields fs) →
    x.erase.map (·.1) = fs.map (·.1)
  | _, .nil => by simp only [SFields.erase, List.map_nil]
  | (f, T) :: _, .cons v rest => by
    simp only [SFields.erase, List.map_cons, SFields.erase_names rest]

theorem lookupBy_map_snd_isNone {β γ : Type} (g : β → γ) (k : Int) :
    (l : List (Int × β)) → (lookupBy k (l.map fun e => (e.1, g e.2))).isNone = (lookupBy k l).isNone
  | [] => rfl
  | (k', v) :: rest => by
    simp only [List.map_cons, lookupBy]
    split
    · rfl
    · exact lookupBy_map_snd_isNone g k rest

theorem nodupKeysB_map_snd {β γ : Type} (g : β → γ) :
    (l : List (Int × β)) → nodupKeysB (l.map fun e => (e.1, g e.2)) = nodupKeysB l
  | [] => rfl
  | (k, v) :: rest => by
    simp only [List.map_cons, nodupKeysB, nodupKeysB_map_snd g rest, lookupBy_map_snd_isNone]

theorem SVal.isDfltB_erase {T : Ty} (d : SVal T) :
    d.erase.isDfltB T = d.beq (SVal.dflt T) := by
  rw [Bool.eq_iff_iff, Semantics.SVal.isDfltB_iff, SVal.beq_iff, ← SVal.dflt_erase]
  exact ⟨SVal.erase_injective, fun h => by rw [h]⟩

theorem SMap.erase_isEmpty {V : Ty} (m : SMap V) : m.erase.isEmpty = m.toList.isEmpty := by
  rw [SMap.erase_eq]; cases m.toList <;> rfl

/-! ## Canonical -/

mutual
theorem SVal.erase_canonB : {T : Ty} → (v : SVal T) → v.erase.canonB T = v.allB canonHB
  | _, .prim (p := .bool) _ => by
    simp only [SVal.erase, SVal.allB, PrimTy.erase, Semantics.SVal.canonB]
  | _, .prim (p := .uint) _ => by
    simp only [SVal.erase, SVal.allB, PrimTy.erase, Semantics.SVal.canonB]
  | _, .prim (p := .int) _ => by
    simp only [SVal.erase, SVal.allB, PrimTy.erase, Semantics.SVal.canonB]
  | _, .struct fs => by
    simp only [SVal.erase, SVal.allB, Semantics.SVal.canonB, SFields.erase_names, decide_true,
      Bool.true_and]
    exact SFields.erase_canonB fs fun _ _ hm => lookupBy_of_nodup (structDef_nodup _) hm
  | _, .array e sh _ => by
    simp only [SVal.erase, SVal.allB, Semantics.SVal.canonB, Bool.not_false, Bool.true_and,
      SVec.erase_canonB e, SList.erase_canonB sh]
    rfl
  | _, @SVal.fixed _ n e => by
    simp only [SVal.erase, SVal.allB, Semantics.SVal.canonB, SVec.length_erase, decide_true,
      Bool.true_and, SVec.erase_canonB e, canonElemsB, Bool.and_true]
    rfl
  | _, .map m d => by
    simp only [SVal.erase, SVal.allB, Semantics.SVal.canonB, SMap.erase_canonB m,
      SVal.erase_canonB d, SVal.isDfltB_erase]
    rw [SMap.erase_eq, nodupKeysB_map_snd]
    show _ = ((nodupKeysB m.toList && d.beq (SVal.dflt _)) && _ && _)
    cases nodupKeysB m.toList <;> cases d.beq (SVal.dflt _) <;> cases m.allB canonHB <;>
      cases d.allB canonHB <;> rfl

theorem SFields.erase_canonB {s : Name} : {fs : List (Name × Ty)} → (x : SFields fs) →
    (∀ f T, (f, T) ∈ fs → lookupBy f (structDef s) = some T) →
    canonFieldsB s x.erase = x.allB canonHB
  | _, .nil, _ => by simp only [SFields.erase, SFields.allB, canonFieldsB]
  | (f, T) :: _, .cons v rest, h => by
    simp only [SFields.erase, SFields.allB, canonFieldsB, h f T List.mem_cons_self,
      SVal.erase_canonB v]
    rw [SFields.erase_canonB rest fun g U hm => h g U (List.mem_cons_of_mem _ hm)]

theorem SList.erase_canonB : {E : Ty} → (l : SList E) → canonElemsB E l.erase = l.allB canonHB
  | _, .nil => by simp only [SList.erase, SList.allB, canonElemsB]
  | _, .cons v rest => by
    simp only [SList.erase, SList.allB, canonElemsB, SVal.erase_canonB v, SList.erase_canonB rest]

theorem SVec.erase_canonB : {E : Ty} → {n : Nat} → (l : SVec E n) →
    canonElemsB E l.erase = l.allB canonHB
  | _, _, .nil => by simp only [SVec.erase, SVec.allB, canonElemsB]
  | _, _, .cons v rest => by
    simp only [SVec.erase, SVec.allB, canonElemsB, SVal.erase_canonB v, SVec.erase_canonB rest]

theorem SMap.erase_canonB : {V : Ty} → (m : SMap V) → canonEntriesB V m.erase = m.allB canonHB
  | _, .nil => by simp only [SMap.erase, SMap.allB, canonEntriesB]
  | _, .cons _ v rest => by
    simp only [SMap.erase, SMap.allB, canonEntriesB, SVal.erase_canonB v, SMap.erase_canonB rest]
end

/-! ## Tight, on a canonical value -/

theorem SVec.erase_isEmpty {E : Ty} {n : Nat} (e : SVec E n) : e.erase.isEmpty = (n == 0) := by
  rw [SVec.erase_eq]
  have := SVec.length_toList e
  cases h : e.toList with
  | nil => rw [h] at this; subst this; rfl
  | cons x xs => rw [h, List.length_cons] at this; subst this; rfl

theorem SList.erase_isEmpty {E : Ty} (l : SList E) : l.erase.isEmpty = l.toList.isEmpty := by
  rw [SList.erase_eq]; cases l.toList <;> rfl

theorem SList.erase_all_isDfltB {E : Ty} (l : SList E) :
    l.erase.all (fun w => w.isDfltB E) = l.toList.all (fun w => w.beq (SVal.dflt E)) := by
  rw [SList.erase_eq, List.all_map]
  congr 1
  funext w
  exact SVal.isDfltB_erase w

mutual
theorem SVal.erase_tightB : {T : Ty} → (v : SVal T) → v.allB canonHB = true →
    v.erase.tightB T = v.allB tightHB
  | _, .prim (p := .bool) _, _ => by simp only [SVal.erase, SVal.allB, PrimTy.erase, Semantics.SVal.tightB]
  | _, .prim (p := .uint) _, _ => by simp only [SVal.erase, SVal.allB, PrimTy.erase, Semantics.SVal.tightB]
  | _, .prim (p := .int) _, _ => by simp only [SVal.erase, SVal.allB, PrimTy.erase, Semantics.SVal.tightB]
  | _, .struct fs, hc => by
    simp only [SVal.allB] at hc
    simp only [SVal.erase, SVal.allB, Semantics.SVal.tightB]
    exact SFields.erase_tightB fs (fun _ _ hm => lookupBy_of_nodup (structDef_nodup _) hm) hc
  | _, .array e sh _, hc => by
    simp only [SVal.allB, Bool.and_eq_true] at hc
    simp only [SVal.erase, SVal.allB, Semantics.SVal.tightB, SVec.erase_isEmpty,
      SList.erase_isEmpty, SList.erase_all_isDfltB, SVec.erase_tightB e hc.1.2,
      SList.erase_tightB sh hc.2]
    rfl
  | _, .fixed e, hc => by
    simp only [SVal.allB, Bool.and_eq_true] at hc
    simp only [SVal.erase, SVal.allB, Semantics.SVal.tightB, List.isEmpty_nil, Bool.true_and,
      SVec.erase_tightB e hc.2]
    rfl
  | _, .map m d, hc => by
    simp only [SVal.allB, Bool.and_eq_true] at hc
    have hcm : (nodupKeysB m.toList && d.beq (SVal.dflt _)) = true := hc.1.1
    rw [Bool.and_eq_true] at hcm
    have hd : d = SVal.dflt _ := (SVal.beq_iff).1 hcm.2
    have hdt : d.allB tightHB = true := by
      rw [hd]; exact (SVal.tightB_iff _).2 (SVal.dflt_tight _)
    simp only [SVal.erase, SVal.allB, Semantics.SVal.tightB, SMap.erase_isEmpty,
      SMap.erase_tightB m hc.1.2, hdt, Bool.and_true]
    rfl

theorem SFields.erase_tightB {s : Name} : {fs : List (Name × Ty)} → (x : SFields fs) →
    (∀ f T, (f, T) ∈ fs → lookupBy f (structDef s) = some T) → x.allB canonHB = true →
    tightFieldsB s x.erase = x.allB tightHB
  | _, .nil, _, _ => by simp only [SFields.erase, SFields.allB, tightFieldsB]
  | (f, T) :: _, .cons v rest, h, hc => by
    simp only [SFields.allB, Bool.and_eq_true] at hc
    simp only [SFields.erase, SFields.allB, tightFieldsB, h f T List.mem_cons_self,
      SVal.erase_tightB v hc.1]
    rw [SFields.erase_tightB rest (fun g U hm => h g U (List.mem_cons_of_mem _ hm)) hc.2]

theorem SList.erase_tightB : {E : Ty} → (l : SList E) → l.allB canonHB = true →
    tightElemsB E l.erase = l.allB tightHB
  | _, .nil, _ => by simp only [SList.erase, SList.allB, tightElemsB]
  | _, .cons v rest, hc => by
    simp only [SList.allB, Bool.and_eq_true] at hc
    simp only [SList.erase, SList.allB, tightElemsB, SVal.erase_tightB v hc.1,
      SList.erase_tightB rest hc.2]

theorem SVec.erase_tightB : {E : Ty} → {n : Nat} → (l : SVec E n) → l.allB canonHB = true →
    tightElemsB E l.erase = l.allB tightHB
  | _, _, .nil, _ => by simp only [SVec.erase, SVec.allB, tightElemsB]
  | _, _, .cons v rest, hc => by
    simp only [SVec.allB, Bool.and_eq_true] at hc
    simp only [SVec.erase, SVec.allB, tightElemsB, SVal.erase_tightB v hc.1,
      SVec.erase_tightB rest hc.2]

theorem SMap.erase_tightB : {V : Ty} → (m : SMap V) → m.allB canonHB = true →
    tightEntriesB V m.erase = m.allB tightHB
  | _, .nil, _ => by simp only [SMap.erase, SMap.allB, tightEntriesB]
  | _, .cons _ v rest, hc => by
    simp only [SMap.allB, Bool.and_eq_true] at hc
    simp only [SMap.erase, SMap.allB, tightEntriesB, SVal.erase_tightB v hc.1,
      SMap.erase_tightB rest hc.2]
end

/-! ## Words and keys -/

theorem Ty.keyFitsB_eq (K : Ty) (k : Int) : Semantics.Ty.keyFitsB K k = K.keyOkB k := by
  cases K with
  | prim p =>
    cases p <;> simp only [Semantics.Ty.keyFitsB, Ty.keyOkB, PrimTy.keyFits, PrimTy.isNumeric,
      Semantics.PrimVal.fits, PrimTy.inRange, Semantics.uintBound, Semantics.intBound,
      Bool.false_eq_true, ↓reduceIte] <;> rfl
  | ref _ => rfl

theorem PrimVal.fits_erase : {p : PrimTy} → (v : p.Denote) →
    Semantics.PrimVal.fits (PrimTy.erase v) p = true
  | .bool, _ => rfl
  | .uint, v => by
    simp only [PrimTy.erase, Semantics.PrimVal.fits, Semantics.uintBound]
    exact v.2
  | .int, v => by
    simp only [PrimTy.erase, Semantics.PrimVal.fits, Semantics.intBound]
    exact v.2

mutual
theorem SVal.erase_wordsB : {T : Ty} → (v : SVal T) → v.erase.wordsB T = v.allB keysHB
  | _, .prim v => by
    simp only [SVal.erase, SVal.allB, Semantics.SVal.wordsB, PrimVal.fits_erase]
  | _, .struct fs => by
    simp only [SVal.erase, SVal.allB, Semantics.SVal.wordsB, SFields.erase_wordsB fs]
  | _, .array e sh _ => by
    simp only [SVal.erase, SVal.allB, Semantics.SVal.wordsB, SVec.erase_wordsB e,
      SList.erase_wordsB sh]
    rfl
  | _, .fixed e => by
    simp only [SVal.erase, SVal.allB, Semantics.SVal.wordsB, SVec.erase_wordsB e, wordsElemsB,
      Bool.and_true]
    rfl
  | _, .map m d => by
    simp only [SVal.erase, SVal.allB, Semantics.SVal.wordsB, SMap.erase_wordsB m,
      SVal.erase_wordsB d]
    rfl

theorem SFields.erase_wordsB : {fs : List (Name × Ty)} → (x : SFields fs) →
    wordsFieldsB x.erase fs = x.allB keysHB
  | _, .nil => by simp only [SFields.erase, SFields.allB, wordsFieldsB]
  | (_, _) :: _, .cons v rest => by
    simp only [SFields.erase, SFields.allB, wordsFieldsB, SVal.erase_wordsB v,
      SFields.erase_wordsB rest]

theorem SList.erase_wordsB : {E : Ty} → (l : SList E) → wordsElemsB E l.erase = l.allB keysHB
  | _, .nil => by simp only [SList.erase, SList.allB, wordsElemsB]
  | _, .cons v rest => by
    simp only [SList.erase, SList.allB, wordsElemsB, SVal.erase_wordsB v, SList.erase_wordsB rest]

theorem SVec.erase_wordsB : {E : Ty} → {n : Nat} → (l : SVec E n) →
    wordsElemsB E l.erase = l.allB keysHB
  | _, _, .nil => by simp only [SVec.erase, SVec.allB, wordsElemsB]
  | _, _, .cons v rest => by
    simp only [SVec.erase, SVec.allB, wordsElemsB, SVal.erase_wordsB v, SVec.erase_wordsB rest]

theorem SMap.erase_wordsB {K : Ty} : {V : Ty} → (m : SMap V) →
    wordsEntriesB K V m.erase = ((m.toList.all fun e => K.keyOkB e.1) && m.allB keysHB)
  | _, .nil => by simp only [SMap.erase, SMap.allB, wordsEntriesB, SMap.toList_nil, List.all_nil,
      Bool.and_self]
  | _, .cons k v rest => by
    simp only [SMap.erase, SMap.allB, wordsEntriesB, SVal.erase_wordsB v, SMap.erase_wordsB rest,
      SMap.toList_cons, List.all_cons, Ty.keyFitsB_eq]
    cases K.keyOkB k <;> cases v.allB keysHB <;> cases (rest.toList.all fun e => K.keyOkB e.1) <;>
      cases rest.allB keysHB <;> rfl
end

/-! ## The storage -/

theorem SVal.erase_shapeB {T : Ty} (v : SVal T) :
    (v.erase.canonB T && v.erase.tightB T) = (v.allB canonHB && v.allB tightHB) := by
  rw [SVal.erase_canonB]
  cases hc : v.allB canonHB with
  | false => rfl
  | true => rw [SVal.erase_tightB v hc]

/-- Every member passes a test, member by member. -/
theorem SFields.allB_iff_mem {B : HeredB} : {fs : List (Name × Ty)} → (hnd : nodupKeysB fs = true) →
    (x : SFields fs) →
    (x.allB B = true ↔ ∀ f T (hm : (f, T) ∈ fs), (x.get (lookupBy_of_nodup hnd hm)).allB B = true)
  | [], _, .nil => by
    simp only [SFields.allB, true_iff]
    intro _ _ hm; exact nomatch hm
  | (f, T) :: fs, hnd, .cons v rest => by
    have hnd' := hnd
    simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hnd'
    simp only [SFields.allB, Bool.and_eq_true]
    rw [SFields.allB_iff_mem hnd'.2 rest]
    constructor
    · rintro ⟨hv, hr⟩ g U hm
      rw [SFields.get_cons]
      by_cases e : g = f
      · subst e
        have hU := SFields.lookupBy_cons_pos rfl (lookupBy_of_nodup hnd hm)
        subst hU
        simp only [dite_true]
        exact hv
      · simp only [e, dite_false]
        rcases List.mem_cons.mp hm with hm | hm
        · exact absurd (congrArg Prod.fst hm) e
        · exact hr g U hm
    · intro h
      refine ⟨?_, fun g U hm => ?_⟩
      · have := h f T List.mem_cons_self
        rw [SFields.get_cons] at this
        simp only [dite_true] at this
        exact this
      · have hgf : g ≠ f := fun he => by
          have := lookupBy_isSome_of_mem' hm
          rw [he, hnd'.1] at this
          exact nomatch this
        have := h g U (List.mem_cons_of_mem _ hm)
        rw [SFields.get_cons] at this
        simp only [hgf, dite_false] at this
        exact this

/-- **`wt(storage)` on a typed storage is its typed test**, for a contract
that declares no root twice. -/
theorem storageWtB_erase (hnd : nodupKeysB C.vars = true) (st : Storage C) :
    storageWtB C.vars st.erase = st.wtB := by
  have hlook : ∀ r T (hm : (r, T) ∈ C.vars),
      lookupBy r st.erase = some (st.get (lookupBy_of_nodup hnd hm)).erase :=
    fun r T hm => SFields.lookupBy_erase st _
  have hshape : storageShapeB C.vars st.erase = st.shapeB := by
    rw [Bool.eq_iff_iff]
    simp only [storageShapeB, Storage.shapeB, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true]
    rw [SFields.allB_iff_mem hnd st, SFields.allB_iff_mem hnd st]
    constructor
    · rintro ⟨-, h⟩
      have h' : ∀ r T (hm : (r, T) ∈ C.vars),
          ((st.get (lookupBy_of_nodup hnd hm)).allB canonHB &&
            (st.get (lookupBy_of_nodup hnd hm)).allB tightHB) = true := by
        intro r T hm
        have := h (r, T) hm
        simp only [hlook r T hm, SVal.erase_shapeB] at this
        exact this
      exact ⟨fun r T hm => (Bool.and_eq_true_iff.1 (h' r T hm)).1,
        fun r T hm => (Bool.and_eq_true_iff.1 (h' r T hm)).2⟩
    · rintro ⟨hc, ht⟩
      refine ⟨SFields.erase_names st, fun rT hm => ?_⟩
      obtain ⟨r, T⟩ := rT
      simp only [hlook r T hm, SVal.erase_shapeB, hc r T hm, ht r T hm, Bool.and_self]
  have hwords : storageWordsB C.vars st.erase = st.keysB := by
    rw [Bool.eq_iff_iff]
    simp only [storageWordsB, Storage.keysB, List.all_eq_true]
    rw [SFields.allB_iff_mem hnd st]
    constructor
    · intro h r T hm
      have := h (r, T) hm
      simp only [hlook r T hm, SVal.erase_wordsB] at this
      exact this
    · intro h rT hm
      obtain ⟨r, T⟩ := rT
      simp only [hlook r T hm, SVal.erase_wordsB]
      exact h r T hm
  rw [storageWtB, hshape, hwords]
  rfl

end Solidity
