import Solidity.Storage.Representation.Members

/-! Array element updates, retained extents and exact header/element frames.
No allocation, runtime copy or compiler numeric-slot operation is introduced. -/
namespace Solidity.Storage.Representation

private theorem element_tail_disjoint {t : STy} {n : Nat} {l x : Loc}
    (tail : Occ (.sarr t n) (l.add t.size) x) (head : Occ t l x) : False := by
  cases tail with
  | @sarr _ _ i _ _ _ hx =>
    have ht : Occ t (l.add ((i + 1) * t.size)) x := by
      simpa only [Loc.add_add, Nat.succ_mul, Nat.add_comm] using hx
    have hh : Occ t (l.add (0 * t.size)) x := by
      simpa only [Nat.zero_mul, Loc.add_zero] using head
    exact occ_sarr_disjoint (Nat.succ_ne_zero i) ht hh

/-- Element replacement preserves the represented whole slot list. -/
theorem ElementsRep.set {E : Ty} {vs : List (SVal E)} {t : STy} {l : Loc} {w replacement : Store}
    (h : ElementsRep vs t l w) (i : Nat) (bound : i < vs.length) (new : SVal E)
    (fresh : ValueRep new t (l.add (i * t.size)) replacement) :
    ElementsRep (vs.set i new) t l (patch w replacement t (l.add (i * t.size))) := by
  induction vs generalizing l i with
  | nil => simp only [List.length_nil] at bound; omega
  | cons v rest ih =>
    cases h with
    | cons _ _ _ _ _ head tail =>
      cases i with
      | zero =>
        simp only [List.set_cons_zero, Nat.zero_mul, Loc.add_zero] at fresh ⊢
        apply ElementsRep.cons
        · exact fresh.replace
        · apply tail.congr
          intro x hx
          exact patch_outside w replacement t l x (element_tail_disjoint hx)
      | succ i =>
        simp only [List.set_cons_succ]
        apply ElementsRep.cons
        · apply head.patch_frame
          intro x hx hy
          have hh : Occ t (l.add (0 * t.size)) x := by
            simpa only [Nat.zero_mul, Loc.add_zero] using hx
          exact occ_sarr_disjoint (i := 0) (i' := i + 1) (Nat.zero_ne_add_one i) hh hy
        · have bound' : i < rest.length := by
            simp only [List.length_cons] at bound; omega
          have fresh' : ValueRep new t ((l.add t.size).add (i * t.size)) replacement := by
            simpa only [Loc.add_add, Nat.succ_mul, Nat.add_comm] using fresh
          simpa only [Loc.add_add, Nat.succ_mul, Nat.add_comm] using ih tail i bound' fresh'

/-- The exact source equation for an arbitrary typed inner fixed-array path. -/
theorem fixed_path_source_save {E U : Ty} {n : Nat} (vs : SVec E n)
    (i : PrimTy.uint.Denote) (p : Path E U) (new : SVal U) (old changed : SVal E)
    (found : vs.toList[i.val.toNat]? = some old) (inner : old.save p new = some changed) :
    (SVal.fixed vs).save (.atF i p) new = some (.fixed (vs.set i.val.toNat changed)) := by
  rw [SVal.save_eq_saveM, SVal.saveM, found]
  rw [SVal.save_eq_saveM] at inner
  simp only [inner, Option.bind_eq_bind, Option.bind_some]

/-- Whole fixed-array representation after a nested-path source save. -/
theorem fixed_path_save {E U : Ty} {n : Nat} {vs : SVec E n} {t : STy} {l : Loc}
    {w replacement : Store} (h : ValueRep (.fixed vs) (.sarr t n) l w)
    (i : PrimTy.uint.Denote) (p : Path E U) (new : SVal U) (old changed : SVal E)
    (found : vs.toList[i.val.toNat]? = some old) (inner : old.save p new = some changed)
    (fresh : ValueRep changed t (l.add (i.val.toNat * t.size)) replacement) :
    (SVal.fixed vs).save (.atF i p) new = some (.fixed (vs.set i.val.toNat changed)) ∧
      ValueRep (.fixed (vs.set i.val.toNat changed)) (.sarr t n) l
        (patch w replacement t (l.add (i.val.toNat * t.size))) := by
  refine ⟨fixed_path_source_save vs i p new old changed found inner, ?_⟩
  cases h with
  | fixed _ _ _ _ shape elements =>
    apply ValueRep.fixed _ _ _ _ shape
    rw [SVec.toList_set]
    exact elements.set i.val.toNat (List.getElem?_eq_some_iff.mp found).1 changed fresh

/-- The source dynamic-array save retains the extent and live prefix length. -/
theorem array_path_source_save {E U : Ty} {n : Nat} (vs : SVec E n) (sh : SList E)
    (hn : n < 2 ^ 256) (i : PrimTy.uint.Denote) (p : Path E U) (new : SVal U)
    (old changed : SVal E) (found : (vs.toList ++ sh.toList)[i.val.toNat]? = some old)
    (inner : old.save p new = some changed) :
    let slots := (vs.toList ++ sh.toList).set i.val.toNat changed
    (SVal.array vs sh hn).save (.at i p) new =
      some (.array (SVec.ofList (slots.take n)) (.ofList (slots.drop n))
        (SVal.take_lt_bound slots hn)) := by
  dsimp only
  rw [SVal.save_eq_saveM, SVal.saveM, found]
  rw [SVal.save_eq_saveM] at inner
  simp only [inner, Option.bind_eq_bind, Option.bind_some]

/-- Whole dynamic-array representation after a nested-path source save. -/
theorem array_path_save {E U : Ty} {n : Nat} {vs : SVec E n} {sh : SList E}
    {hn : n < 2 ^ 256} {t : STy} {l : Loc} {w replacement : Store}
    (h : ValueRep (.array vs sh hn) (.darr t) l w)
    (i : PrimTy.uint.Denote) (p : Path E U) (new : SVal U) (old changed : SVal E)
    (found : (vs.toList ++ sh.toList)[i.val.toNat]? = some old)
    (inner : old.save p new = some changed)
    (fresh : ValueRep changed t (.data l (i.val.toNat * t.size)) replacement) :
    let slots := (vs.toList ++ sh.toList).set i.val.toNat changed
    (SVal.array vs sh hn).save (.at i p) new =
      some (.array (SVec.ofList (slots.take n)) (.ofList (slots.drop n))
        (SVal.take_lt_bound slots hn)) ∧
    ValueRep (.array (SVec.ofList (slots.take n)) (.ofList (slots.drop n))
      (SVal.take_lt_bound slots hn)) (.darr t) l
      (patch w replacement t (.data l (i.val.toNat * t.size))) := by
  dsimp only
  refine ⟨array_path_source_save vs sh hn i p new old changed found inner, ?_⟩
  cases h with
  | array _ _ _ _ _ _ shape live extent header elements =>
    have le : n ≤ (vs.toList ++ sh.toList).length := by
      rw [List.length_append, SVec.length_toList]; omega
    have length : (((vs.toList ++ sh.toList).set i.val.toNat changed).take n).length = n := by
      rw [List.length_take, List.length_set, Nat.min_eq_left le]
    apply ValueRep.array _ _ _ _ _ _ shape
    · simpa only [length] using live
    · simpa only [SVec.toList_ofList, SList.toList_ofList, List.take_append_drop,
        List.length_set] using extent
    · rw [patch_outside _ _ _ _ _ (fun hx => occ_darr_len_elem hx)]
      simpa only [length] using header
    · rw [SVec.toList_ofList, SList.toList_ofList, List.take_append_drop]
      have fresh' : ValueRep changed t ((Loc.data l 0).add (i.val.toNat * t.size)) replacement := by
        simpa only [Loc.add, Nat.zero_add] using fresh
      have updated : ElementsRep ((vs.toList ++ sh.toList).set i.val.toNat changed) t (.data l 0)
          (patch w replacement t ((Loc.data l 0).add (i.val.toNat * t.size))) :=
        elements.set i.val.toNat (List.getElem?_eq_some_iff.mp found).1 changed fresh'
      simpa only [Loc.add, Nat.zero_add] using updated

/-- Element replacement never overwrites the dynamic length header. -/
theorem array_header_patch_frame (w replacement : Store) (t : STy) (l : Loc) (i : Nat) :
    patch w replacement t (.data l (i * t.size)) l = w l :=
  patch_outside _ _ _ _ _ (fun hx => occ_darr_len_elem hx)

/-- Nested values of distinct elements frame each other's replacement. -/
theorem array_other_element_frame {E : Ty} {v : SVal E} {t : STy} {l : Loc}
    {i j : Nat} {w replacement : Store} (h : ValueRep v t (.data l (i * t.size)) w)
    (different : i ≠ j) : ValueRep v t (.data l (i * t.size))
      (patch w replacement t (.data l (j * t.size))) :=
  h.patch_frame (fun _ hx hy => occ_darr_disjoint different hx hy)

/-- A live array length encoded as a supported full word. -/
def lengthWord (n : Nat) (hn : n < 2 ^ 256) : Semantics.Word :=
  ⟨n, by simp only [PrimTy.inRange, decide_eq_true_eq]; omega⟩

/-- Changing the live/shadow partition of the same retained slots changes only
its header word. This is not a proof of allocation or runtime copying. -/
theorem array_repartition {E : Ty} {n n' : Nat} {vs : SVec E n} {sh : SList E}
    {hn : n < 2 ^ 256} {t : STy} {l : Loc} {w : Store}
    (h : ValueRep (.array vs sh hn) (.darr t) l w)
    (vs' : SVec E n') (sh' : SList E) (hn' : n' < 2 ^ 256)
    (same_slots : vs'.toList ++ sh'.toList = vs.toList ++ sh.toList) :
    ValueRep (.array vs' sh' hn') (.darr t) l (write w l (lengthWord n' hn')) := by
  cases h with
  | array _ _ _ _ _ _ shape _ extent _ elements =>
    apply ValueRep.array _ _ _ _ _ _ shape
    · have le : n' ≤ (vs.toList ++ sh.toList).length := by
        rw [← same_slots, List.length_append, SVec.length_toList]; omega
      exact Nat.le_trans le extent
    · simpa only [same_slots] using extent
    · rw [write_same]
      rfl
    · rw [same_slots]
      apply elements.congr
      intro x hx
      apply write_other
      intro eq
      subst x
      cases hx with
      | @sarr _ _ i _ _ _ he =>
        apply occ_darr_len_elem (i := i)
        simpa only [Loc.add, Nat.zero_add] using he

/-- A successful live read agrees with the represented element as well. -/
theorem array_live_read {E : Ty} {n : Nat} {vs : SVec E n} {sh : SList E}
    {hn : n < 2 ^ 256} {t : STy} {l : Loc} {w : Store}
    (h : ValueRep (.array vs sh hn) (.darr t) l w) {i : PrimTy.uint.Denote} {v : SVal E}
    (found : vs.toList[i.val.toNat]? = some v) :
    (SVal.array vs sh hn).findLive (.at i .nil) = some v ∧
      ValueRep v t (.data l (i.val.toNat * t.size)) w := by
  constructor
  · rw [SVal.findLive_eq_findLiveM, SVal.findLiveM, found]
    change v.findLiveM .nil = some v
    rw [← SVal.findLive_eq_findLiveM]
    rfl
  · apply (array_read h (i := i) (v := v) ?_).2
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found

/-- Source fixed-array writes fail beyond the source bound. -/
theorem fixed_save_missing {E U : Ty} {n : Nat} (vs : SVec E n) (i : PrimTy.uint.Denote)
    (p : Path E U) (new : SVal U) (bound : n ≤ i.val.toNat) :
    (SVal.fixed vs).save (.atF i p) new = none := by
  rw [SVal.save_eq_saveM, SVal.saveM,
    List.getElem?_eq_none (by rw [SVec.length_toList]; exact bound)]

/-- Source alias writes fail only past the retained extent, not the live end. -/
theorem array_save_missing {E U : Ty} {n : Nat} (vs : SVec E n) (sh : SList E)
    (hn : n < 2 ^ 256) (i : PrimTy.uint.Denote) (p : Path E U) (new : SVal U)
    (bound : (vs.toList ++ sh.toList).length ≤ i.val.toNat) :
    (SVal.array vs sh hn).save (.at i p) new = none := by
  rw [SVal.save_eq_saveM, SVal.saveM, List.getElem?_eq_none bound]

/-- A normal live read rejects retained shadow slots. -/
theorem array_live_missing {E U : Ty} {n : Nat} (vs : SVec E n) (sh : SList E)
    (hn : n < 2 ^ 256) (i : PrimTy.uint.Denote) (p : Path E U) (bound : n ≤ i.val.toNat) :
    (SVal.array vs sh hn).findLive (.at i p) = none := by
  rw [SVal.findLive_eq_findLiveM, SVal.findLiveM,
    List.getElem?_eq_none (by rw [SVec.length_toList]; exact bound)]

end Solidity.Storage.Representation
