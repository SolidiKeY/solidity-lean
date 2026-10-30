import Solidity.Backend.MemoryOps.CalldataUintScheduleGrowth
import Solidity.Backend.MemoryOps.CalldataSequenceFixtures

namespace Solidity.Backend.MemoryOps.UintScheduleControls
open SequenceFixtures
private def eight : U := ⟨8,by decide⟩
private def nine : U := ⟨9,by decide⟩
def repair : SnapshotArgs := (2,3,1)
def repairs (copies : Nat) : List SnapshotArgs := repair::List.replicate copies repair

theorem repair_origin (k : Nat) : snapshotOrigin repair k = if k=1 then 2 else k := by
  by_cases hk : k=1
  · subst k; rfl
  · rw [if_neg hk]
    unfold snapshotOrigin repair
    change (if 1 ≤ k ∧ k < 1+(3-2) then 2+(k-1) else k) = k
    rw [if_neg (by omega)]

theorem repairs_origin (copies k : Nat) : captureOrigin (repairs copies) k = if k=1 then 2 else k := by
  induction copies with
  | zero => exact repair_origin k
  | succ copies ih =>
    change snapshotOrigin repair (captureOrigin (repairs copies) k) = _
    rw [ih,repair_origin]
    by_cases hk : k=1
    · rw [if_pos hk,if_neg (by decide)]
    · rw [if_neg hk,if_neg hk]

/-- INITIAL-value calculation only: actual immutable uint payload and backward
indices, independent of any execution or desired final equality. -/
theorem initial_agreement (tail : List U) (copies : Nat) : ∀ k,
    (replaceSlice ([seven,eight,eight]++tail) 1 (([nine].drop 0).take (1-0)))[captureOrigin (repairs copies) k]? = ([seven,eight,eight]++tail)[k]? := by
  intro k
  rw [repairs_origin]
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k => rw [if_neg (by omega)]; rfl

/-- One actual decoded transfer and arbitrary runtime recaptures on either
published dynamic or fixed array. Contents are input fixture facts, not a
postrelation, payload conversion or preservation hypothesis. -/
theorem repair_restores {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .uint)) (tail : List U)
    (hc : MObj.elems a (hp.get r) = [seven,eight,eight]++tail) (copies : Nat) :
    checkedUintCaptures (uints [nine]) 9 hp r a 0 1 1 (repairs copies) = some hp := by
  have hlen : 3 ≤ hp.len r a := by
    unfold Heap.len
    rw [hc,List.length_append]
    simp only [List.length_cons,List.length_nil]
    omega
  have hi := checkedCalldataUints_some (uint_repr [nine]) hp r a 0 1 1
    ⟨by decide,by decide⟩ (by omega)
  have hv : CapturesValid (hp.len r a) (repairs copies) := by
    intro x hx
    have he : x=repair := by
      rcases List.mem_cons.mp hx with h | h
      · exact h
      · exact (List.mem_replicate.mp h).2
    subst x
    change 2 ≤ 3 ∧ 3 ≤ hp.len r a ∧ 1+(3-2) ≤ hp.len r a
    omega
  obtain ⟨out,ho⟩ := (checkedUintCaptures_success (uints [nine]) 9 hp r a 0 1 1 _).mpr ⟨⟨_,hi⟩,hv⟩
  have ha : ∃ bs, calldataUints (uints [nine]) 9 = some bs ∧ ∀ k,
      (replaceSlice (MObj.elems a (hp.get r)) 1 ((bs.drop 0).take (1-0)))[captureOrigin (repairs copies) k]? =
        (MObj.elems a (hp.get r))[k]? := by
    refine ⟨[nine],?_,?_⟩
    · rw [calldataUints_lookup (uint_repr [nine]),calldataUint_values]
    · rw [hc]; exact initial_agreement tail copies
  have he := (checkedUintCaptures_restore (uints [nine]) 9 hp r a 0 1 1 _ out ho).mpr ha
  exact ho.trans (congrArg some he)

private abbrev A : RefTy := .array (.prim .uint)
private abbrev P : RefTy := .fixed (.ref A) 2
private abbrev H : HTy := [A,A,P]
private def r : HRef H A := ⟨0,rfl⟩
private def neighbor : HRef H A := ⟨1,rfl⟩
private def parent : HRef H P := ⟨2,rfl⟩
private def old (n : Nat) := [seven,eight,eight]++List.replicate n maximum
private def hp (n : Nat) (hn : n+3<2^256) : Heap H :=
  (⟨old n,by simp only [old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,
    ⟨[maximum,zero,one],by decide⟩,⟨[r,r],rfl⟩,())
private theorem hlen (n : Nat) (hn : n+3<2^256) : (hp n hn).len r .dyn = n+3 := by
  simp only [Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn,old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
private def mid (n : Nat) (hn : n+3<2^256) (v : U) := overwriteSlice (hp n hn) r .dyn 1 [v]
  (by rw [hlen]; change 1+1 ≤ n+3; omega)

theorem decoded_first (n : Nat) (hn : n+3<2^256) (v : U) :
    checkedCalldataUints (uints [v]) 9 (hp n hn) r .dyn 0 1 1 = some (mid n hn v) := by
  have h := checkedCalldataUints_some (uint_repr [v]) (hp n hn) r .dyn 0 1 1
    ⟨by decide,by simp only [List.length_cons,List.length_nil]; decide⟩ (by rw [hlen]; omega)
  simpa only [mid,calldataUint_values,List.drop_zero,List.take_succ_cons,List.take_zero] using h

theorem runtime (n copies : Nat) (hn : n+3<2^256) :
    checkedUintCaptures (uints [nine]) 9 (hp n hn) r .dyn 0 1 1 (repairs copies) = some (hp n hn) :=
  repair_restores _ r .dyn _ (by simp only [MObj.elems_dyn]; rfl) copies

/-- Complete initial/decoded/final/neighbor/alias-root observations, including
actual decoded Some and actual reached finite schedule Some. -/
theorem ordered (n copies : Nat) (hn : n+3<2^256) :
    checkedCalldataUints (uints [nine]) 9 (hp n hn) r .dyn 0 1 1 = some (mid n hn nine) ∧
    runCaptures (mid n hn nine) r .dyn (repairs copies) = some (hp n hn) ∧
    MObj.elems .dyn ((hp n hn).get r) = old n ∧
    MObj.elems .dyn ((mid n hn nine).get r) = [seven,nine,eight]++List.replicate n maximum ∧
    MObj.elems .dyn ((mid n hn nine).get neighbor) = [maximum,zero,one] ∧
    (MObj.elems .fixed ((mid n hn nine).get parent)).map HRef.id = [0,0] ∧
    (MObj.elems .fixed ((hp n hn).get parent)).map HRef.id = [0,0] := by
  have hi := decoded_first n hn nine
  obtain ⟨m,hfirst,hrest⟩ := (checkedUintCaptures_some _ _ _ _ _ _ _ _ _ _).mp (runtime n copies hn)
  have he : m=mid n hn nine := Option.some.inj (hfirst.symm.trans hi)
  subst m
  refine ⟨hi,hrest,?_,?_,?_,?_,?_⟩
  · simp only [MObj.elems_dyn]; rfl
  · dsimp only [mid]
    rw [overwriteSlice_elems]; simp only [MObj.elems_dyn]; rfl
  · dsimp only [mid]
    rw [overwriteSlice_frame _ r neighbor .dyn 1 _ _ (by decide)]
    simp only [MObj.elems_dyn]; rfl
  · dsimp only [mid]
    rw [overwriteSlice_frame _ r parent .dyn 1 _ _ (by decide)]
    simp only [MObj.elems_fixed]; rfl
  · simp only [MObj.elems_fixed]; rfl

private abbrev F : RefTy := .fixed (.prim .uint) 3
private def fr : HRef [F] F := ⟨0,rfl⟩
private def fhp : Heap [F] := (⟨[seven,eight,eight],rfl⟩,())
theorem fixed_runtime (copies : Nat) :
    checkedUintCaptures (uints [nine]) 9 fhp fr .fixed 0 1 1 (repairs copies) = some fhp :=
  repair_restores _ fr .fixed [] (by simp only [MObj.elems_fixed]; rfl) copies

theorem fixed_ordered (copies : Nat) :
    ∃ m, checkedCalldataUints (uints [nine]) 9 fhp fr .fixed 0 1 1 = some m ∧
      runCaptures m fr .fixed (repairs copies) = some fhp ∧
      MObj.elems .fixed (m.get fr) = [seven,nine,eight] ∧
      MObj.elems .fixed (fhp.get fr) = [seven,eight,eight] := by
  obtain ⟨m,hfirst,hrest⟩ := (checkedUintCaptures_some _ _ _ _ _ _ _ _ _ _).mp (fixed_runtime copies)
  refine ⟨m,hfirst,hrest,?_,?_⟩
  · rw [checkedCalldataUints_elems (uint_repr [nine]) fhp fr .fixed 0 1 1 m hfirst,calldataUint_values]
    simp only [MObj.elems_fixed]; rfl
  · simp only [MObj.elems_fixed]; rfl

/-- Maximum-word extraction survives without truncation and is read back from
the ACTUAL immutable source object, not a caller conversion hypothesis. -/
theorem high_word (n : Nat) (hn : n+3<2^256) :
    checkedUintCaptures (uints [maximum]) 9 (hp n hn) r .dyn 0 1 1 [] = some (mid n hn maximum) ∧
    ∃ v, (MObj.elems .dyn ((mid n hn maximum).get r))[1]? = some v ∧
      DecodedArrayRead (uints [maximum]) 9 (.int .u256) none 0 (.val (sourceUint v)) := by
  have ho : checkedUintCaptures (uints [maximum]) 9 (hp n hn) r .dyn 0 1 1 [] = some (mid n hn maximum) := by
    unfold checkedUintCaptures
    rw [decoded_first,Option.bind_some]; rfl
  exact ⟨ho,checkedUintCaptures_source_read _ _ _ _ _ _ _ _ (uint_repr [maximum]) [] _ ho 1 (by decide)⟩

/-- Every final read directly instantiates the new complete provenance law. -/
theorem all_reads (n copies : Nat) (hn : n+3<2^256) :
    ∃ bs, calldataUints (uints [nine]) 9 = some bs ∧ ∀ k,
      (MObj.elems .dyn ((hp n hn).get r))[k]? =
        (replaceSlice (MObj.elems .dyn ((hp n hn).get r)) 1 ((bs.drop 0).take (1-0)))[captureOrigin (repairs copies) k]? :=
  checkedUintCaptures_read _ _ _ _ _ _ _ _ _ _ (runtime n copies hn)

/-- Independently invalid initial guards, including missing input before any
recapture; no source halt or rollback is asserted. -/
theorem transfer_failures (n : Nat) (hn : n+3<2^256) (xs : List SnapshotArgs) :
    checkedUintCaptures (uints [nine]) 10 (hp n hn) r .dyn 0 1 1 xs = none ∧
    checkedUintCaptures (uints [nine]) 9 (hp n hn) r .dyn 1 0 0 xs = none ∧
    checkedUintCaptures (uints [nine]) 9 (hp n hn) r .dyn 0 2 0 xs = none ∧
    checkedUintCaptures (uints [nine]) 9 (hp n hn) r .dyn 0 1 (n+3) xs = none ∧
    checkedUintCaptures (bools [true]) 7 (hp n hn) r .dyn 0 1 1 xs = none := by
  have h0 : checkedCalldataUints (uints [nine]) 10 (hp n hn) r .dyn 0 1 1 = none := by rfl
  have h1 := (checkedCalldataUints_none_iff (uint_repr [nine]) (hp n hn) r .dyn 1 0 0).mpr (Or.inl (by decide))
  have h2 := (checkedCalldataUints_none_iff (uint_repr [nine]) (hp n hn) r .dyn 0 2 0).mpr (Or.inr (Or.inl (by decide)))
  have h3 := (checkedCalldataUints_none_iff (uint_repr [nine]) (hp n hn) r .dyn 0 1 (n+3)).mpr
    (Or.inr (Or.inr (by rw [hlen]; omega)))
  have h4 : checkedCalldataUints (bools [true]) 7 (hp n hn) r .dyn 0 1 1 = none := by rfl
  simp only [checkedUintCaptures,h0,h1,h2,h3,h4,Option.bind_none,and_self]

theorem late_failure (n : Nat) (hn : n+3<2^256) :
    checkedCalldataUints (uints [nine]) 9 (hp n hn) r .dyn 0 1 1 = some (mid n hn nine) ∧
    runCaptures (mid n hn nine) r .dyn [repair] = some (hp n hn) ∧
    checkedCaptureOverwrite (hp n hn) r .dyn r .dyn 0 1 (n+3) = none ∧
    checkedUintCaptures (uints [nine]) 9 (hp n hn) r .dyn 0 1 1 [repair,(0,1,n+3),repair] = none := by
  have hpre : runCaptures (mid n hn nine) r .dyn [repair] = some (hp n hn) := (ordered n 0 hn).2.1
  have hb : checkedCaptureOverwrite (hp n hn) r .dyn r .dyn 0 1 (n+3) = none := by
    rw [checkedCaptureOverwrite_none_iff,hlen]; omega
  refine ⟨decoded_first n hn nine,hpre,hb,?_⟩
  unfold checkedUintCaptures
  rw [decoded_first,Option.bind_some]
  change runCaptures (mid n hn nine) r .dyn ([repair]++[(0,1,n+3),repair]) = _
  rw [runCaptures_append,hpre,Option.bind_some]
  change (checkedCaptureOverwrite (hp n hn) r .dyn r .dyn 0 1 (n+3)).bind _ = _
  rw [hb,Option.bind_none]

theorem empty_end (n : Nat) (hn : n+3<2^256) :
    checkedUintCaptures (uints []) 9 (hp n hn) r .dyn 0 0 (n+3) [] = some (hp n hn) ∧
    checkedUintCaptures (uints []) 9 (hp n hn) r .dyn 0 0 (n+3) [(n+3,n+3,n+3)] = some (hp n hn) := by
  have hi := checkedCalldataUints_empty (uint_repr []) (hp n hn) r .dyn 0 (n+3)
    (by decide) (by rw [hlen]; exact Nat.le_refl _)
  have he : checkedCaptureOverwrite (hp n hn) r .dyn r .dyn (n+3) (n+3) (n+3) = some (hp n hn) := by
    have h := checkedCaptureOverwrite_some (hp n hn) r .dyn r .dyn (n+3) (n+3) (n+3)
      ⟨Nat.le_refl _,by rw [hlen]; exact Nat.le_refl _⟩ (by rw [hlen]; omega)
    simpa only [captureOverwrite,sliceElems,Nat.sub_self,List.take_zero,overwriteSlice_empty] using h
  simp only [checkedUintCaptures,hi,Option.bind_some,runCaptures,he,and_self]

theorem skipped_negative (n : Nat) (hn : n+3<2^256) :
    checkedUintCaptures (uints [nine]) 9 (hp n hn) r .dyn 0 1 1 [] = some (mid n hn nine) ∧
    MObj.elems .dyn ((mid n hn nine).get r) = [seven,nine,eight]++List.replicate n maximum ∧
    mid n hn nine ≠ hp n hn := by
  have ho : checkedUintCaptures (uints [nine]) 9 (hp n hn) r .dyn 0 1 1 [] = some (mid n hn nine) := by
    unfold checkedUintCaptures; rw [decoded_first,Option.bind_some]; rfl
  refine ⟨ho,(ordered n 0 hn).2.2.2.1,?_⟩
  intro he
  have hv := congrArg (fun h : Heap H => (MObj.elems .dyn (h.get r))[1]?) he
  dsimp only at hv
  rw [(ordered n 0 hn).2.2.2.1] at hv
  simp only [MObj.elems_dyn] at hv
  change (some nine : Option U)=some eight at hv
  have hnine := congrArg (fun v : U => v.val) (Option.some.inj hv)
  change (9 : Int)=8 at hnine
  contradiction

private abbrev Q : RefTy := .array (.ref A)
private def obj : MObj H Q := ⟨[r,neighbor,r],by decide⟩
private def e := List.prefix_append H [Q]
/-- Actual allocation after decoded mutation, then actual arbitrary repair.
Fresh own references frame while the referenced child changes from nine to eight. -/
theorem allocated_interstage (n copies : Nat) (hn : n+3<2^256) :
    ∃ m out, checkedCalldataUints (uints [nine]) 9 (hp n hn) r .dyn 0 1 1 = some m ∧
      MObj.elems .dyn (m.get r) = [seven,nine,eight]++List.replicate n maximum ∧
      runCaptures (m.alloc obj).1 (r.wk e) .dyn (repairs copies) = some out ∧
      MObj.elems .dyn (out.get (r.wk e)) = old n ∧
      MObj.elems .dyn (out.get (neighbor.wk e)) = [maximum,zero,one] ∧
      (MObj.elems .dyn (out.get (m.alloc obj).2)).map HRef.id = [0,1,0] ∧
      (r.wk e).id ≠ (m.alloc obj).2.id := by
  obtain ⟨m,out,hfirst,hrest,hk,hfresh⟩ := checkedUintCaptures_interstage_alloc
    (uints [nine]) 9 (hp n hn) (hp n hn) r .dyn 0 1 1 _ (runtime n copies hn) obj
  have he : m=mid n hn nine := Option.some.inj (hfirst.symm.trans (decoded_first n hn nine))
  have hm := (ordered n copies hn).2.2.2.1
  rw [← he] at hm
  refine ⟨m,out,hfirst,hm,hrest,?_,?_,?_,old_ne_fresh m obj r⟩
  · rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .uint)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [hk neighbor,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .uint)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [hfresh,Heap.get_alloc,MObj.elems_wk,List.map_map]
    simp only [MObj.elems_dyn]; rfl

theorem boundary33 :
    checkedUintCaptures (uints [nine]) 9 (hp 33 (by decide)) r .dyn 0 1 1 (repairs 4) = some (hp 33 (by decide)) ∧
    (MObj.elems .dyn ((hp 33 (by decide)).get r))[32]? = some maximum := by
  refine ⟨runtime 33 4 (by decide),?_⟩
  simp only [MObj.elems_dyn]; rfl

theorem high_exact (n : Nat) (hn : n+3<2^256) :
    MObj.elems .dyn ((mid n hn maximum).get r) = [seven,maximum,eight]++List.replicate n maximum ∧
    (MObj.elems .dyn ((mid n hn maximum).get r))[1]? = some maximum ∧
    maximum.val = ((2^256-1 : Nat) : Int) := by
  have hv : MObj.elems .dyn ((mid n hn maximum).get r) = [seven,maximum,eight]++List.replicate n maximum := by
    dsimp only [mid]; rw [overwriteSlice_elems]; simp only [MObj.elems_dyn]; rfl
  refine ⟨hv,?_,rfl⟩
  rw [hv]; rfl

/-- This recapture reads the CHANGED decoded cell, unlike the restoration
fixture's unchanged index2. Frozen initial8 produces a different full vector. -/
theorem changed_source_negative (n : Nat) (hn : n+3<2^256) :
    ∃ out frozen : Heap H,
      checkedUintCaptures (uints [nine]) 9 (hp n hn) r .dyn 0 1 1 [(1,2,0)] = some out ∧
      MObj.elems .dyn (out.get r) = [nine,nine,eight]++List.replicate n maximum ∧
      MObj.elems .dyn (frozen.get r) = [eight,nine,eight]++List.replicate n maximum ∧
      MObj.elems .dyn (out.get neighbor) = [maximum,zero,one] ∧
      (MObj.elems .fixed (out.get parent)).map HRef.id = [0,0] ∧ frozen ≠ out := by
  have hv : CapturesValid ((hp n hn).len r .dyn) [(1,2,0)] := by
    intro x hx
    have he : x=(1,2,0) := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hx
    subst x
    change 1 ≤ 2 ∧ 2 ≤ (hp n hn).len r .dyn ∧ 0+(2-1) ≤ (hp n hn).len r .dyn
    rw [hlen]; omega
  obtain ⟨out,ho⟩ := (checkedUintCaptures_success (uints [nine]) 9 (hp n hn) r .dyn 0 1 1 _).mpr
    ⟨⟨mid n hn nine,decoded_first n hn nine⟩,hv⟩
  obtain ⟨bs,hb,hr⟩ := checkedUintCaptures_read _ _ _ _ _ _ _ _ _ out ho
  have hb' := calldataUints_lookup (uint_repr [nine])
  rw [calldataUint_values] at hb'
  have he : bs=[nine] := Option.some.inj (hb.symm.trans hb')
  subst bs
  have hout : MObj.elems .dyn (out.get r) = [nine,nine,eight]++List.replicate n maximum := by
    apply List.ext_getElem?
    intro k
    rw [hr k]
    simp only [MObj.elems_dyn]
    change ([seven,nine,eight]++List.replicate n maximum)[snapshotOrigin (1,2,0) k]? =
      ([nine,nine,eight]++List.replicate n maximum)[k]?
    cases k with
    | zero => rfl
    | succ k =>
      have he : snapshotOrigin (1,2,0) (k+1) = k+1 := by
        unfold snapshotOrigin
        change (if 0 ≤ k+1 ∧ k+1 < 0+(2-1) then 1+(k+1-0) else k+1)=k+1
        rw [if_neg (by omega)]
      rw [he]; rfl
  let frozen := overwriteSlice (mid n hn nine) r .dyn 0 [eight]
    (by dsimp only [mid]; rw [overwriteSlice_len,hlen]; change 0+1 ≤ n+3; omega)
  have hfrozen : MObj.elems .dyn (frozen.get r) = [eight,nine,eight]++List.replicate n maximum := by
    dsimp only [frozen]
    rw [overwriteSlice_elems,(ordered n 0 hn).2.2.2.1]; rfl
  refine ⟨out,frozen,ho,hout,hfrozen,?_,?_,?_⟩
  · rw [checkedUintCaptures_frame _ _ _ _ _ _ _ _ _ _ ho neighbor (by decide)]
    simp only [MObj.elems_dyn]; rfl
  · rw [checkedUintCaptures_frame _ _ _ _ _ _ _ _ _ _ ho parent (by decide)]
    simp only [MObj.elems_fixed]; rfl
  · intro he
    have he' := congrArg (fun h : Heap H => (MObj.elems .dyn (h.get r))[0]?) he
    dsimp only at he'
    rw [hout,hfrozen] at he'
    change (some eight : Option U)=some nine at he'
    have hnine := congrArg (fun v : U => v.val) (Option.some.inj he')
    change (8 : Int)=9 at hnine
    contradiction

/-- Direct positive application of the new decoded-composition Keeps law to
an ACTUAL initial allocation, with fresh own-field frame and full old vectors. -/
theorem initial_allocated (n copies : Nat) (hn : n+3 < 2^256) :
    ∃ out, checkedUintCaptures (uints [nine]) 9 ((hp n hn).alloc obj).1 (r.wk e) .dyn 0 1 1
        (repairs copies) = some out ∧ Heap.Keeps e (hp n hn) out ∧
      MObj.elems .dyn (out.get (r.wk e)) = old n ∧
      MObj.elems .dyn (out.get (neighbor.wk e)) = [maximum,zero,one] ∧
      (MObj.elems .dyn (out.get ((hp n hn).alloc obj).2)).map HRef.id = [0,1,0] ∧
      (r.wk e).id ≠ ((hp n hn).alloc obj).2.id := by
  have ho : checkedUintCaptures (uints [nine]) 9 (hp n hn) r .dyn 0 1 1 _ = some (hp n hn) :=
    UintScheduleControls.runtime n copies hn
  obtain ⟨out,ho',hk⟩ := checkedUintCaptures_keeps (uint_repr [nine]) e (Heap.keeps_alloc (hp n hn) obj)
    r .dyn 0 1 1 _ (hp n hn) ho
  refine ⟨out,ho',hk,?_,?_,?_,old_ne_fresh (hp n hn) obj r⟩
  · rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .uint)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [hk neighbor,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .uint)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [checkedUintCaptures_frame _ _ _ _ _ _ _ _ _ _ ho' ((hp n hn).alloc obj).2
      (old_ne_fresh (hp n hn) obj r),Heap.get_alloc,MObj.elems_wk,List.map_map]
    simp only [MObj.elems_dyn]; rfl

/-- Actual initial allocation preserves the complete ordered failure trace:
decoded Some, nonempty repair prefix Some, reached invalid call None, full None. -/
theorem rejected_alloc (n : Nat) (hn : n+3 < 2^256) :
    ∃ mid reached, checkedCalldataUints (uints [nine]) 9 ((hp n hn).alloc obj).1 (r.wk e) .dyn 0 1 1 = some mid ∧
      runCaptures mid (r.wk e) .dyn [repair] = some reached ∧
      checkedCaptureOverwrite reached (r.wk e) .dyn (r.wk e) .dyn 0 1 (n+3) = none ∧
      checkedUintCaptures (uints [nine]) 9 ((hp n hn).alloc obj).1 (r.wk e) .dyn 0 1 1
        [repair,(0,1,n+3),repair] = none := by
  have hfirst := (UintScheduleControls.late_failure n hn).1
  obtain ⟨mid,hfirst',hk1⟩ := checkedCalldataUints_keeps (uint_repr [nine]) e
    (Heap.keeps_alloc (hp n hn) obj) r .dyn 0 1 1 _ hfirst
  obtain ⟨reached,hpre,hk2⟩ := runCaptures_keeps e hk1 r .dyn [repair] (hp n hn)
    (UintScheduleControls.late_failure n hn).2.1
  refine ⟨mid,reached,hfirst',hpre,?_,?_⟩
  · exact (checkedCaptureOverwrite_none_keeps e hk2 r .dyn r .dyn 0 1 (n+3)).mpr
      (UintScheduleControls.late_failure n hn).2.2.1
  · apply (checkedUintCaptures_none_keeps (uint_repr [nine]) e (Heap.keeps_alloc (hp n hn) obj) r .dyn 0 1 1 _).mpr
    exact (UintScheduleControls.late_failure n hn).2.2.2
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.fixed_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fixed_ordered
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.repair_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms repair_origin
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.repairs_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms repairs_origin
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.initial_agreement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms initial_agreement
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.repair_restores' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms repair_restores
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.decoded_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decoded_first
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runtime
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.fixed_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fixed_runtime
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.high_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms high_word
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.all_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms all_reads
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.transfer_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms transfer_failures
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.late_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms late_failure
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.empty_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_end
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.skipped_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms skipped_negative
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.allocated_interstage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms allocated_interstage
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.boundary33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boundary33
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.high_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms high_exact
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.changed_source_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_source_negative
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.initial_allocated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms initial_allocated
/-- info: 'Solidity.Backend.MemoryOps.UintScheduleControls.rejected_alloc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rejected_alloc
end Solidity.Backend.MemoryOps.UintScheduleControls
