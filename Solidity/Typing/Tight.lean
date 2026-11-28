import Solidity.Typing.Reachability


namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}


def tightH : Hered where
  arr := fun {E} {n} _ sh => (E.defaultOkS = false → n = 0 ∧ sh = .nil) ∧
    (E.isPrimitive = true → ∀ w ∈ sh.toList, w = SVal.dflt E)
  fix _ _ := True
  map _ := fun _ _ => True

abbrev SVal.Tight {T : Ty} (v : SVal T) : Prop := v.All tightH

abbrev Storage.Tight (st : Storage C) : Prop := st.All tightH

theorem SVal.defaultOf_of_prim {E : Ty} (hE : E.isPrimitive = true) (x : SVal E) :
    x.defaultOf = SVal.dflt E := by
  cases E with
  | prim p => cases x; simp only [SVal.defaultOf, SVal.dflt_prim]
  | ref _ => exact nomatch hE

theorem pushSlot_snd_sub {E : Ty} : {l : List (SVal E)} → ∀ w ∈ (pushSlot E l).2, w ∈ l
  | [], _, h => nomatch h
  | _ :: _, _, h => List.mem_cons_of_mem _ h

theorem SVec.toList_eq_nil {E : Ty} {n : Nat} (e : SVec E n) (h : n = 0) : e.toList = [] :=
  List.eq_nil_of_length_eq_zero (by rw [SVec.length_toList]; exact h)

theorem SVal.dflt_tight (T : Ty) : (SVal.dflt T).Tight :=
  SVal.dflt_all (P := tightH)
    (fun _ => ⟨fun _ => ⟨rfl, rfl⟩, fun _ w hw => by rw [SList.toList_nil] at hw; exact nomatch hw⟩)
    (fun _ _ => trivial) (fun _ _ => trivial) T

theorem SRef.okDeep {U : Ty} (r : SRef C U) : U.okDeep = true :=
  Path.okDeep r.path (C.root_okDeep r.hroot)

theorem tight_of_plainArr {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (_ : n < 2 ^ 256)
    (hE : E.okDeep = true)
    (hsh : plainH.arr e sh) : tightH.arr e sh := by
  have hsh' : sh = .nil := hsh
  subst hsh'
  refine ⟨fun hd => ?_, fun _ w hw => ?_⟩
  · rw [okDeep_defaultOkS hE] at hd; exact nomatch hd
  · rw [SList.toList_nil] at hw; exact nomatch hw

theorem tightH_run : HeredRun tightH (fun T => T.okDeep = true) where
  save e sh i x hi hlive harr _ := by
    refine ⟨fun hd => ?_, fun hp w hw => ?_⟩
    · obtain ⟨hn, hsh⟩ := harr.1 hd
      subst hsh
      rw [SVec.toList_eq_nil e hn, SList.toList_nil] at hi
      exact absurd hi (Nat.not_lt_zero _)
    · rw [SList.toList_ofList, List.drop_set, if_pos (hlive hp),
        List.drop_left' (SVec.length_toList e)] at hw
      exact harr.2 hp w hw
  map _ _ _ _ _ _ := trivial
  strip _ sh harr _ :=
    ⟨fun hd => ⟨(harr.1 hd).1, rfl⟩, fun _ w hw => by rw [SList.toList_nil] at hw; exact nomatch hw⟩
  del e sh harr _ := by
    refine ⟨fun hd => ⟨rfl, ?_⟩, fun hp w hw => ?_⟩
    · obtain ⟨hn, hsh⟩ := harr.1 hd
      subst hsh
      rw [SVec.toList_defaultOf, SVec.toList_eq_nil e hn, SList.toList_nil]
      rfl
    · rw [SList.toList_ofList] at hw
      rcases List.mem_append.mp hw with hw | hw
      · rw [SVec.toList_defaultOf] at hw
        obtain ⟨u, -, rfl⟩ := List.mem_map.mp hw
        exact SVal.defaultOf_of_prim hp u
      · exact harr.2 hp w hw
  ov oel osh nel nsh ho hn _ _ _ := by
    refine ⟨fun hd => ⟨(hn.1 hd).1, ?_⟩, fun hp w hw => ?_⟩
    · obtain ⟨hm, hosh⟩ := ho.1 hd
      subst hosh
      rw [SVec.toList_eq_nil oel hm, SList.toList_nil]
      simp only [List.drop_nil, List.map_nil, List.append_nil]
      rfl
    · rw [SList.toList_ofList] at hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨u, -, rfl⟩ := List.mem_map.mp hw
        exact SVal.defaultOf_of_prim hp u
      · exact ho.2 hp w (List.mem_of_mem_drop hw)
  push e sh x hG _ harr _ _ _ := by
    refine ⟨fun hd => ?_, fun hp w hw => ?_⟩
    · rw [okDeep_defaultOkS (by simpa only [Ty.okDeep] using hG)] at hd; exact nomatch hd
    · rw [SList.toList_ofList] at hw
      exact harr.2 hp w (pushSlot_snd_sub w hw)
  pop e sh last keep hlast hkeep harr _ _ := by
    refine ⟨fun hd => ?_, fun hp w hw => ?_⟩
    · rw [SVec.toList_eq_nil e (harr.1 hd).1] at hlast; exact nomatch hlast
    · rw [SList.toList_ofList] at hw
      rcases List.mem_cons.mp hw with hw | hw
      · cases keep with
        | true => rw [hkeep rfl] at hp; exact nomatch hp
        | false => rw [hw]; exact SVal.defaultOf_of_prim hp last
      · exact harr.2 hp w hw
  dflt := SVal.dflt_tight
  plain v hT h := SVal.all_mono_deep (P := tightH) (Q := plainH) tight_of_plainArr
    (fun _ _ _ _ => trivial) (fun _ _ _ h => h.elim) v hT h

theorem Storage.init_tight : (Storage.init C).Tight :=
  SFields.dflt_all (P := tightH)
    (fun _ => ⟨fun _ => ⟨rfl, rfl⟩, fun _ w hw => by rw [SList.toList_nil] at hw; exact nomatch hw⟩)
    (fun _ _ => trivial) (fun _ _ => trivial) C.vars

abbrev tightInv (C : Contract) : RunInv C := heredInv C tightH

theorem Prog.run_tight {Γ Γ' : Ctx} (P : Prog C Γ Γ') {σ : State C Γ}
    {o : Out C σ.H Γ'} (hσ : (tightInv C).HoldsT σ) (h : P.run σ = .ok o) :
    o.st.storage.Tight :=
  Prog.run_all tightH_run SRef.okDeep P hσ h

theorem reachable_tight {st : Storage C} (h : Reachable C st) : st.Tight :=
  Reachable.all tightH_run SRef.okDeep Storage.init_tight h


def fitsH : Hered where
  arr := fun {_} {n} _ sh => n + sh.length < 2 ^ 256
  fix _ n := n ≤ 2 ^ 256
  map _ := fun _ _ => True

abbrev SVal.Fits {T : Ty} (v : SVal T) : Prop := v.All fitsH

abbrev Storage.Fits (st : Storage C) : Prop := st.All fitsH

end Solidity
