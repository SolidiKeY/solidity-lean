import Solidity.Typing.Tight


namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}


def bndH : Hered where
  arr := fun {_} {n} _ sh => n + sh.length < 2 ^ 256
  fix _ _ := True
  map _ := fun _ _ => True

abbrev SVal.Bnd {T : Ty} (v : SVal T) : Prop := v.All bndH

abbrev Storage.Bnd (st : Storage C) : Prop := st.All bndH

theorem SList.length_ofList {E : Ty} (l : List (SVal E)) : (SList.ofList l).length = l.length := by
  simp only [SList.length, SList.toList_ofList]

theorem SList.length_nil {E : Ty} : (SList.nil (E := E)).length = 0 := by
  simp only [SList.length, SList.toList_nil, List.length_nil]

theorem bndH_nil (E : Ty) : bndH.arr (SVec.nil (E := E)) (SList.nil (E := E)) := by
  show 0 + SList.length SList.nil < 2 ^ 256
  rw [SList.length_nil]; decide

theorem SVal.dflt_bnd (T : Ty) : (SVal.dflt T).Bnd :=
  SVal.dflt_all (P := bndH) bndH_nil (fun _ _ => trivial)
    (fun _ _ => trivial) T

theorem bndH_run : HeredRun bndH (fun _ => True) where
  save e sh i x hi _ harr _ := by
    show (List.take _ _).length + (SList.ofList _).length < _
    rw [SList.length_ofList, List.length_take, List.length_drop, List.length_set,
      List.length_append, SVec.length_toList]
    have : sh.toList.length = sh.length := rfl
    have harr' : _ + sh.length < 2 ^ 256 := harr
    omega
  map _ _ _ _ _ _ := trivial
  strip _ _ harr _ := by
    show _ + SList.length .nil < _
    rw [SList.length_nil]
    have harr' : _ + _ < 2 ^ 256 := harr
    omega
  del e sh harr _ := by
    show 0 + (SList.ofList _).length < _
    rw [SList.length_ofList, List.length_append, SVec.length_toList]
    have : sh.toList.length = sh.length := rfl
    have harr' : _ + sh.length < 2 ^ 256 := harr
    omega
  ov oel osh nel nsh ho hn _ _ _ := by
    show _ + (SList.ofList _).length < _
    rw [SList.length_ofList, List.length_append, List.length_map, List.length_drop,
      List.length_drop, SVec.length_toList]
    have h1 : osh.toList.length = osh.length := rfl
    have ho' : _ + osh.length < 2 ^ 256 := ho
    have hn' : _ + nsh.length < 2 ^ 256 := hn
    omega
  push e sh x _ hb harr _ _ _ := by
    show (e.toList ++ [x]).length + (SList.ofList _).length < _
    rw [SList.length_ofList, List.length_append, SVec.length_toList, List.length_singleton]
    have harr' : _ + sh.length < 2 ^ 256 := harr
    have : sh.toList.length = sh.length := rfl
    cases hs : sh.toList with
    | nil => simp only [pushSlot, List.length_nil]; omega
    | cons c rest =>
      rw [hs, List.length_cons] at this
      simp only [pushSlot] at this ⊢
      omega
  pop e sh last keep hlast _ harr _ _ := by
    show (e.toList.dropLast).length + (SList.ofList _).length < _
    rw [SList.length_ofList, List.length_dropLast, List.length_cons, SVec.length_toList]
    have hpos : 0 < e.toList.length := List.length_pos_of_mem hlast
    rw [SVec.length_toList] at hpos
    have : sh.toList.length = sh.length := rfl
    have harr' : _ + sh.length < 2 ^ 256 := harr
    omega
  dflt := SVal.dflt_bnd
  plain v _ h := SVal.all_mono' (P := bndH) (Q := plainH)
    (fun _ sh hn hsh => by
      have hsh' : sh = .nil := hsh
      subst hsh'
      show _ + SList.length .nil < _
      rw [SList.length_nil]; omega)
    (fun _ _ _ => trivial) (fun _ _ h => h.elim) v h

theorem Storage.init_bnd : (Storage.init C).Bnd :=
  SFields.dflt_all (P := bndH) bndH_nil (fun _ _ => trivial) (fun _ _ => trivial) C.vars

abbrev fitsInv (C : Contract) : RunInv C := heredInv C bndH

theorem Prog.run_bnd {Γ Γ' : Ctx} (P : Prog C Γ Γ') {σ : State C Γ} {o : Out C σ.H Γ'}
    (hσ : (fitsInv C).HoldsT σ) (h : P.run σ = .ok o) : o.st.storage.Bnd :=
  Prog.run_all bndH_run (fun _ => trivial) P hσ h

theorem reachable_bnd {st : Storage C} (h : Reachable C st) : st.Bnd :=
  Reachable.all bndH_run (fun _ => trivial) Storage.init_bnd h


def FixedFitsAt (T : Ty) : Prop := ∀ E n, Path T (.ref (.fixed E n)) → n ≤ 2 ^ 256

def FixedFits (C : Contract) : Prop := ∀ nt ∈ C.vars, FixedFitsAt nt.2

theorem fixedFits_mono : fitsH.Mono bndH FixedFitsAt :=
  ⟨fun _ hT _ hm E n p => hT E n (.field (lookupBy_of_nodup (structDef_nodup _) hm) p),
    fun _ hT E n p => hT E n (.at (PrimTy.dflt _) p),
    fun _ _ hT E n p => hT E n (.atF (PrimTy.dflt _) p),
    fun _ _ hT E n p => hT E n (.key (PrimTy.dflt _) p),
    fun _ _ _ _ h => h, fun E n hT _ => hT E n .nil, fun _ _ _ h => h⟩

theorem SVal.fits_of_bnd {T : Ty} (v : SVal T) (hT : FixedFitsAt T) (h : v.Bnd) : v.Fits :=
  SVal.all_mono (P := fitsH) (Q := bndH) (G := FixedFitsAt) fixedFits_mono v hT h

theorem Storage.fits_of_bnd (hf : FixedFits C) (st : Storage C) (h : st.Bnd) : st.Fits :=
  SFields.all_mono (P := fitsH) (Q := bndH) (G := FixedFitsAt) fixedFits_mono st hf h

theorem reachable_fits (hf : FixedFits C) {st : Storage C} (h : Reachable C st) : st.Fits :=
  Storage.fits_of_bnd hf st (reachable_bnd h)

end Solidity
