import Solidity.Storage.Representation.Frames
import Solidity.Storage.Representation.Words

/-! Symbolic subtree replacement and mapping source-save laws.
`patch` is an abstract store update; no runtime copying/allocation cost is
claimed. Scalar footprints reduce it to a single word write. -/
namespace Solidity.Storage.Representation

noncomputable def patch (w new : Store) (t : STy) (l : Loc) : Store := by
  classical
  exact fun x => if Occ t l x then new x else w x

theorem patch_inside (w new : Store) (t : STy) (l x : Loc) (h : Occ t l x) :
    patch w new t l x = new x := by
  classical
  exact if_pos h

theorem patch_outside (w new : Store) (t : STy) (l x : Loc) (h : ¬ Occ t l x) :
    patch w new t l x = w x := by
  classical
  exact if_neg h

/-- A represented replacement is represented in the patched store. -/
theorem ValueRep.replace {T : Ty} {v : SVal T} {t : STy} {l : Loc} {w new : Store}
    (h : ValueRep v t l new) : ValueRep v t l (patch w new t l) :=
  h.congr (fun x hx => patch_inside w new t l x hx)

/-- Every disjoint subtree frames a replacement, at arbitrary nested depth. -/
theorem ValueRep.patch_frame {T : Ty} {v : SVal T} {t u : STy} {l r : Loc}
    {w new : Store} (h : ValueRep v t l w)
    (disjoint : ∀ x, Occ t l x → Occ u r x → False) :
    ValueRep v t l (patch w new u r) :=
  h.congr (fun x hx => patch_outside w new u r x (disjoint x hx))

theorem saveM_nil {T : Ty} (v new : SVal T) : v.saveM .nil new = some new := by
  cases v <;> rfl

/-- The source's mapping replacement remains independent of word updates. -/
theorem mapping_source_save {K : PrimTy} {V : Ty} (entries : SMap K V)
    (d new : SVal V) (k : K.Denote) :
    (SVal.map entries d).save (.key k .nil) new =
      some (.map (.ofList (Semantics.setBy k new entries.toList)) d) := by
  rw [SVal.save_eq_saveM, SVal.saveM]
  cases Semantics.lookupBy k entries.toList <;> simp only [saveM_nil, Option.bind_eq_bind, Option.bind_some]

/-- A mapping-entry replacement changes exactly its existing occupied region. -/
theorem mapping_save {K : PrimTy} {V : Ty} {entries : SMap K V} {d new : SVal V}
    {t : STy} {l : Loc} {w replacement : Store}
    (old : ValueRep (.map entries d) (.map t) l w) (k : K.Denote)
    (fresh : ValueRep new t (.hash (keyWord k) l 0) replacement) :
    ValueRep (.map (.ofList (Semantics.setBy k new entries.toList)) d) (.map t) l
      (patch w replacement t (.hash (keyWord k) l 0)) := by
  cases old with
  | mapping _ _ _ _ _ shape values =>
    apply ValueRep.mapping _ _ _ _ _ shape
    intro q
    rw [SMap.toList_ofList]
    by_cases eq : q = k
    · subst q
      rw [Semantics.lookupBy_setBy_self, Option.getD_some]
      exact fresh.replace
    · rw [Semantics.lookupBy_setBy_ne eq]
      apply (values q).patch_frame
      intro x hx hy
      exact occ_keys_disjoint (fun he => eq (keyWord_inj he)) hx hy

/-- One mapping step composes an arbitrary already-proved typed path save. -/
theorem mapping_path_source_save {K : PrimTy} {V U : Ty} (entries : SMap K V)
    (d changed : SVal V) (k : K.Denote) (p : Path V U) (new : SVal U)
    (inner : ((Semantics.lookupBy k entries.toList).getD d).save p new = some changed) :
    (SVal.map entries d).save (.key k p) new =
      some (.map (.ofList (Semantics.setBy k changed entries.toList)) d) := by
  rw [SVal.save_eq_saveM, SVal.saveM]
  rw [SVal.save_eq_saveM] at inner
  cases he : Semantics.lookupBy k entries.toList <;>
    simp only [he, Option.getD_none, Option.getD_some] at inner ⊢ <;>
    simp only [inner, Option.bind_eq_bind, Option.bind_some]

/-- Source path composition and symbolic representation compose together. -/
theorem mapping_path_save {K : PrimTy} {V U : Ty} {entries : SMap K V}
    {d changed : SVal V} {t : STy} {l : Loc} {w replacement : Store}
    (old : ValueRep (.map entries d) (.map t) l w) (k : K.Denote)
    (p : Path V U) (new : SVal U)
    (inner : ((Semantics.lookupBy k entries.toList).getD d).save p new = some changed)
    (fresh : ValueRep changed t (.hash (keyWord k) l 0) replacement) :
    (SVal.map entries d).save (.key k p) new =
      some (.map (.ofList (Semantics.setBy k changed entries.toList)) d) ∧
    ValueRep (.map (.ofList (Semantics.setBy k changed entries.toList)) d) (.map t) l
      (patch w replacement t (.hash (keyWord k) l 0)) :=
  ⟨mapping_path_source_save entries d changed k p new inner, mapping_save old k fresh⟩

end Solidity.Storage.Representation
