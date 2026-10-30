import Solidity.Backend.MemoryOps.CalldataRestoration
import Solidity.Backend.MemoryOps.CalldataSequenceFixtures

/-! Actual two-write restoration with a genuinely broken intermediate child,
runtime tails and repeated root aliases. Existing decoded tables, no ABI code. -/
namespace Solidity.Backend.MemoryOps.RestorationControls
open SequenceFixtures
private abbrev B := BoolChildRef
private abbrev C := RefChildRef
private abbrev H : HTy := [B,B,C]
private def neighbor : HRef H B := ⟨0,rfl⟩
private def child : HRef H B := ⟨1,rfl⟩
private def root : HRef H C := ⟨2,rfl⟩
private def address (i : Nat) := 100+i
private def old (n : Nat) := [false,true,false] ++ List.replicate n false
private def hp (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) : Heap H :=
  (⟨[true,false],by decide⟩,
   ⟨old n,by simp only [old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,
   ⟨List.replicate m child,by simpa only [List.length_replicate] using hm⟩,())
private def sv : Source.Data D BoolChildTy := .val (.cdRef rfl 101)
private def rv : Source.Data D RefChildTy := .val (.cdRef rfl 102)
private def table (n m : Nat) : Source.Calldata D := ⟨[],fun off =>
  if off = 101 then some ⟨BoolChildTy,decodedBools (old n)⟩ else
  if off = 102 then some ⟨RefChildTy,decodedChildRefs address (List.replicate m child)⟩ else none⟩
private theorem initial (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    BoolChildRepr (table n m) address (hp n m hn hm) sv child := by
  refine ⟨rfl,?_⟩; simp only [MObj.elems_dyn]; rfl
private theorem root_initial (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    RefChildRepr (table n m) address (hp n m hn hm) rv root := by
  refine ⟨rfl,?_,?_⟩
  · simp only [MObj.elems_dyn]; rfl
  · intro leaf hl
    have h : leaf ∈ List.replicate m child := by simpa only [MObj.elems_dyn] using hl
    have he := (List.mem_replicate.mp h).2
    subst leaf
    exact initial n m hn hm
private def firstPayload : List Bool := [false,false]
private def secondPayload : List Bool := [true,false]
private theorem cap1 (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    0+firstPayload.length ≤ (hp n m hn hm).len child .dyn := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,child,old,firstPayload,
    List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
private theorem cap2 (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    1+secondPayload.length ≤ (hp n m hn hm).len child .dyn := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,child,old,secondPayload,
    List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
private def mid (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :=
  overwriteSlice (hp n m hn hm) child .dyn 0 firstPayload (cap1 n m hn hm)
private def out (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :=
  overwriteIntervals (hp n m hn hm) child .dyn 0 firstPayload (cap1 n m hn hm) 1 secondPayload (cap2 n m hn hm)

private theorem actual_single (bs : List Bool) (h : Heap H) (d : Nat)
    (hd : d+bs.length ≤ h.len child .dyn) :
    checkedCalldataBools (bools bs) 7 h child .dyn 0 bs.length d = some (overwriteSlice h child .dyn d bs hd) := by
  have ho := checkedCalldataBools_some (bool_repr bs) h child .dyn 0 bs.length d ⟨by omega,by omega⟩ (by simpa only [Nat.sub_zero] using hd)
  simpa only [bool_values,List.drop_zero,Nat.sub_zero,List.take_length] using ho
private theorem actual_pair (bs cs : List Bool) (h : Heap H) (d f : Nat)
    (hd : d+bs.length ≤ h.len child .dyn) (he : f+cs.length ≤ h.len child .dyn) :
    checkedBoolSequence (bools bs) 7 (bools cs) 7 h child .dyn 0 bs.length d child .dyn 0 cs.length f =
      some (overwriteIntervals h child .dyn d bs hd f cs he) := by
  have ho := checkedBoolSequence_same_checked (bool_repr bs) (bool_repr cs) h child .dyn
    0 bs.length d 0 cs.length f ⟨by omega,by omega⟩ (by simpa only [Nat.sub_zero] using hd)
    ⟨by omega,by omega⟩ (by simpa only [Nat.sub_zero] using he)
  simpa only [bool_values,List.drop_zero,Nat.sub_zero,List.take_length] using ho
private theorem reached (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    checkedBoolSequence (bools firstPayload) 7 (bools secondPayload) 7 (hp n m hn hm)
      child .dyn 0 2 0 child .dyn 0 2 1 = some (out n m hn hm) :=
  actual_pair firstPayload secondPayload _ 0 1 (cap1 n m hn hm) (cap2 n m hn hm)

/-- Agreement is checked against INITIAL values only. The first overwritten
intersection need not agree, because the second write repairs it. -/
theorem criterion (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    BoolSequenceRestores (bools firstPayload) 7 (bools secondPayload) 7 (hp n m hn hm)
      child .dyn 0 2 0 0 2 1 := by
  unfold BoolSequenceRestores
  rw [calldataBools_lookup (bool_repr firstPayload),calldataBools_lookup (bool_repr secondPayload)]
  rw [bool_values,bool_values]
  change LastWriteAgrees (MObj.elems .dyn ((hp n m hn hm).get child)) 0 firstPayload 1 secondPayload
  constructor
  · intro i hi
    have he : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases he with rfl | rfl <;> simp only [MObj.elems_dyn] <;> rfl
  · intro i hi hx
    have he : i = 0 := by change i < 2 at hi; change 0+i < 1 ∨ 1+2 ≤ 0+i at hx; omega
    subst i
    simp only [MObj.elems_dyn]; rfl

/-- Actual first Some, fully changed intermediate contents and broken child
correspondence; the second actual Some restores the entire heap by the criterion. -/
theorem break_then_restore (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    checkedCalldataBools (bools firstPayload) 7 (hp n m hn hm) child .dyn 0 2 0 = some (mid n m hn hm) ∧
    MObj.elems .dyn ((mid n m hn hm).get child) = [false,false,false] ++ List.replicate n false ∧
    ¬ BoolChildRepr (table n m) address (mid n m hn hm) sv child ∧
    checkedBoolSequence (bools firstPayload) 7 (bools secondPayload) 7 (hp n m hn hm)
      child .dyn 0 2 0 child .dyn 0 2 1 = some (out n m hn hm) ∧
    out n m hn hm = hp n m hn hm := by
  refine ⟨actual_single firstPayload _ 0 (cap1 n m hn hm),?_,?_,reached n m hn hm,?_⟩
  · dsimp only [mid]
    rw [overwriteSlice_elems]; simp only [MObj.elems_dyn]; rfl
  · intro hf
    have he := (initial n m hn hm).object_eq hf
    have hv := congrArg (fun o : MObj H B => (MObj.elems .dyn o)[1]?) he
    dsimp only at hv
    dsimp only [mid] at hv
    rw [overwriteSlice_elems] at hv
    have bad : (some false : Option Bool) ≠ some true := by decide
    simp only [MObj.elems_dyn] at hv
    exact bad hv
  · exact (boolSequence_heap_restore_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ (reached n m hn hm)).mpr (criterion n m hn hm)

/-- Final selected repeated aliases and the original immutable table are
restored without any mid-heap correspondence premise. -/
theorem represented (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    BoolChildRepr (table n m) address (out n m hn hm) sv child ∧
    RefChildRepr (table n m) address (out n m hn hm) rv root := by
  constructor
  · exact ((initial n m hn hm).sequence_restore_iff (bools firstPayload) 7 (bools secondPayload) 7 0 2 0 0 2 1 _ (reached n m hn hm)).mpr (criterion n m hn hm)
  · apply (root_initial n m hn hm).sequence_restore (bools firstPayload) 7 (bools secondPayload) 7 child .dyn 0 2 0 0 2 1 _ (reached n m hn hm)
    intro leaf hl
    exact Or.inr (criterion n m hn hm)

/-- Complete intermediate/final child, neighbor and reference identity vectors. -/
theorem observations (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    MObj.elems .dyn ((mid n m hn hm).get neighbor) = [true,false] ∧
    (MObj.elems .dyn ((mid n m hn hm).get root)).map HRef.id = List.replicate m 1 ∧
    MObj.elems .dyn ((out n m hn hm).get child) = old n ∧
    MObj.elems .dyn ((out n m hn hm).get neighbor) = [true,false] ∧
    (MObj.elems .dyn ((out n m hn hm).get root)).map HRef.id = List.replicate m 1 := by
  have he := (break_then_restore n m hn hm).2.2.2.2
  rw [he]
  constructor
  · dsimp only [mid]
    rw [overwriteSlice_frame _ child neighbor .dyn 0 firstPayload _ (by decide)]
    simp only [MObj.elems_dyn]; rfl
  constructor
  · dsimp only [mid]
    rw [overwriteSlice_frame _ child root .dyn 0 firstPayload _ (by decide)]
    simp only [MObj.elems_dyn]
    change (List.replicate m child).map HRef.id = List.replicate m 1
    rw [List.map_replicate]; rfl
  refine ⟨?_,?_,?_⟩
  · simp only [MObj.elems_dyn]; rfl
  · simp only [MObj.elems_dyn]; rfl
  · simp only [MObj.elems_dyn]
    change (List.replicate m child).map HRef.id = List.replicate m 1
    rw [List.map_replicate]; rfl

private theorem extracted (bs cs : List Bool) (h : Heap H) (d f : Nat) :
    BoolSequenceRestores (bools bs) 7 (bools cs) 7 h child .dyn 0 bs.length d 0 cs.length f ↔
      LastWriteAgrees (MObj.elems .dyn (h.get child)) d bs f cs := by
  unfold BoolSequenceRestores
  rw [calldataBools_lookup (bool_repr bs),calldataBools_lookup (bool_repr cs)]
  simp only [bool_values,List.drop_zero,Nat.sub_zero,List.take_length]

/-- The reached second operation acts on the genuinely changed intermediate. -/
theorem second_reached (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    checkedCalldataBools (bools secondPayload) 7 (mid n m hn hm) child .dyn 0 2 1 = some (out n m hn hm) := by
  obtain ⟨mid',hf,hs⟩ := (checkedBoolSequence_some_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp (reached n m hn hm)
  have he := Option.some.inj ((actual_single firstPayload _ 0 (cap1 n m hn hm)).symm.trans hf)
  rw [← he] at hs
  exact hs

/-- A wrong last payload leaves a successful but unrepresented final child. -/
theorem changed_final_negative (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    ∃ bad, checkedBoolSequence (bools firstPayload) 7 (bools firstPayload) 7 (hp n m hn hm)
      child .dyn 0 2 0 child .dyn 0 2 1 = some bad ∧
      MObj.elems .dyn (bad.get child) = [false,false,false] ++ List.replicate n false ∧
      ¬ BoolChildRepr (table n m) address bad sv child := by
  have hc : 1+firstPayload.length ≤ (hp n m hn hm).len child .dyn := cap2 n m hn hm
  let bad := overwriteIntervals (hp n m hn hm) child .dyn 0 firstPayload (cap1 n m hn hm) 1 firstPayload hc
  have ho := actual_pair firstPayload firstPayload (hp n m hn hm) 0 1 (cap1 n m hn hm) hc
  have ha : ¬ BoolSequenceRestores (bools firstPayload) 7 (bools firstPayload) 7 (hp n m hn hm) child .dyn 0 2 0 0 2 1 := by
    intro h
    have hx := ((extracted firstPayload firstPayload _ 0 1).mp h).1 0 (by decide)
    have bad : (some false : Option Bool) ≠ some true := by decide
    simp only [MObj.elems_dyn] at hx
    exact bad hx
  refine ⟨bad,ho,?_,?_⟩
  · dsimp only [bad,overwriteIntervals]
    rw [overwriteSlice_elems,overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl
  · intro h
    exact ha (((initial n m hn hm).sequence_restore_iff _ _ _ _ _ _ _ _ _ _ bad ho).mp h)

/-- Repairing a different cell does not repair the first write's surviving bad
cell. This exercises the FIRST-survivor half of the criterion. -/
theorem incomplete_negative (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    ∃ bad, checkedBoolSequence (bools firstPayload) 7 (bools [false]) 7 (hp n m hn hm)
      child .dyn 0 2 0 child .dyn 0 1 2 = some bad ∧
      MObj.elems .dyn (bad.get child) = [false,false,false] ++ List.replicate n false ∧
      ¬ BoolChildRepr (table n m) address bad sv child := by
  have hc : 2+([false] : List Bool).length ≤ (hp n m hn hm).len child .dyn := cap2 n m hn hm
  let bad := overwriteIntervals (hp n m hn hm) child .dyn 0 firstPayload (cap1 n m hn hm) 2 [false] hc
  have ho := actual_pair firstPayload [false] (hp n m hn hm) 0 2 (cap1 n m hn hm) hc
  have ha : ¬ BoolSequenceRestores (bools firstPayload) 7 (bools [false]) 7 (hp n m hn hm) child .dyn 0 2 0 0 1 2 := by
    intro h
    have hx := ((extracted firstPayload [false] _ 0 2).mp h).2 1 (by decide) (Or.inl (by decide))
    have bad : (some false : Option Bool) ≠ some true := by decide
    simp only [MObj.elems_dyn] at hx
    exact bad hx
  refine ⟨bad,ho,?_,?_⟩
  · dsimp only [bad,overwriteIntervals]
    rw [overwriteSlice_elems,overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl
  · intro h
    exact ha (((initial n m hn hm).sequence_restore_iff _ _ _ _ _ _ _ _ _ _ bad ho).mp h)

/-- Reversing these overlapping operations produces a different final heap and
loses the original child correspondence. -/
theorem wrong_order_negative (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    ∃ bad, checkedBoolSequence (bools secondPayload) 7 (bools firstPayload) 7 (hp n m hn hm)
      child .dyn 0 2 1 child .dyn 0 2 0 = some bad ∧
      MObj.elems .dyn (bad.get child) = [false,false,false] ++ List.replicate n false ∧
      ¬ BoolChildRepr (table n m) address bad sv child ∧ bad ≠ out n m hn hm := by
  let bad := overwriteIntervals (hp n m hn hm) child .dyn 1 secondPayload (cap2 n m hn hm) 0 firstPayload (cap1 n m hn hm)
  have ho := actual_pair secondPayload firstPayload (hp n m hn hm) 1 0 (cap2 n m hn hm) (cap1 n m hn hm)
  have ha : ¬ BoolSequenceRestores (bools secondPayload) 7 (bools firstPayload) 7 (hp n m hn hm) child .dyn 0 2 1 0 2 0 := by
    intro h
    have hx := ((extracted secondPayload firstPayload _ 1 0).mp h).1 1 (by decide)
    have bad : (some false : Option Bool) ≠ some true := by decide
    simp only [MObj.elems_dyn] at hx
    exact bad hx
  have hbad : ¬ BoolChildRepr (table n m) address bad sv child := by
    intro h
    exact ha (((initial n m hn hm).sequence_restore_iff _ _ _ _ _ _ _ _ _ _ bad ho).mp h)
  refine ⟨bad,ho,?_,hbad,?_⟩
  · dsimp only [bad,overwriteIntervals]
    rw [overwriteSlice_elems,overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl
  · intro he
    rw [he] at hbad
    exact hbad (represented n m hn hm).1

/-- All valid root indices retain their typed shared identity; selected0/32
instances below are nonempty even though m0 is also admitted. -/
theorem typed_aliases (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256)
    (i : U) (hi : i.val.toNat < m) :
    (mid n m hn hm).index root .dyn i = some child ∧
    (out n m hn hm).index root .dyn i = some child ∧
    (out n m hn hm).index child .dyn zero = some false ∧
    (out n m hn hm).index child .dyn one = some true := by
  change (MObj.elems .dyn ((mid n m hn hm).get root))[i.val.toNat]? = some child ∧
    (MObj.elems .dyn ((out n m hn hm).get root))[i.val.toNat]? = some child ∧ _
  have he := (break_then_restore n m hn hm).2.2.2.2
  rw [he]
  have hr : (mid n m hn hm).get root = (hp n m hn hm).get root := by
    dsimp only [mid]; exact overwriteSlice_frame _ child root .dyn 0 firstPayload _ (by decide)
  rw [hr]
  have hx : (MObj.elems .dyn ((hp n m hn hm).get root))[i.val.toNat]? = some child := by
    simp only [MObj.elems_dyn]
    change (List.replicate m child)[i.val.toNat]? = some child
    exact List.getElem?_replicate_of_lt hi
  refine ⟨hx,hx,?_,?_⟩
  all_goals change (MObj.elems .dyn ((hp n m hn hm).get child))[_]? = _
  all_goals simp only [MObj.elems_dyn]; rfl

/-- Empty exact-end intervals and touching nonempty intervals execute as
actual decoded sequences and satisfy the same initial-footprint criterion. -/
theorem endpoints (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    checkedBoolSequence (bools []) 7 (bools []) 7 (hp n m hn hm)
      child .dyn 0 0 (n+3) child .dyn 0 0 (n+3) = some (hp n m hn hm) ∧
    checkedBoolSequence (bools [false]) 7 (bools secondPayload) 7 (hp n m hn hm)
      child .dyn 0 1 0 child .dyn 0 2 1 = some (hp n m hn hm) := by
  have hlen : (hp n m hn hm).len child .dyn = n+3 := by
    simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,child,old,
      List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
  constructor
  · have hd : n+3+([] : List Bool).length ≤ (hp n m hn hm).len child .dyn := by rw [hlen]; simp only [List.length_nil,Nat.add_zero]; exact Nat.le_refl _
    have ho := actual_pair [] [] (hp n m hn hm) (n+3) (n+3) hd hd
    have ha : BoolSequenceRestores (bools []) 7 (bools []) 7 (hp n m hn hm) child .dyn 0 0 (n+3) 0 0 (n+3) := by
      apply (extracted [] [] _ _ _).mpr
      constructor <;> intro i hi <;> cases hi
    have he := (boolSequence_heap_restore_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho).mpr ha
    exact ho.trans (congrArg some he)
  · have hd : 0+([false] : List Bool).length ≤ (hp n m hn hm).len child .dyn := by rw [hlen]; simp only [List.length_cons,List.length_nil]; omega
    have ho := actual_pair [false] secondPayload (hp n m hn hm) 0 1 hd (cap2 n m hn hm)
    have ha : BoolSequenceRestores (bools [false]) 7 (bools secondPayload) 7 (hp n m hn hm) child .dyn 0 1 0 0 2 1 := by
      apply (extracted [false] secondPayload _ _ _).mpr
      constructor
      · intro i hi
        have he : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
        rcases he with rfl | rfl <;> simp only [MObj.elems_dyn] <;> rfl
      · intro i hi hx
        have he : i = 0 := by change i < 1 at hi; omega
        subst i
        simp only [MObj.elems_dyn]; rfl
    have he := (boolSequence_heap_restore_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho).mpr ha
    exact ho.trans (congrArg some he)

/-- The generic typed criterion also restores nonprimitive identities. The
first root-slot write changes child to neighbor; the second restores child. -/
theorem reference_restore (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) (hm0 : 0 < m) :
    ∃ (hd : 0+([neighbor] : List (HRef H B)).length ≤ (hp n m hn hm).len root .dyn)
      (he : 0+([child] : List (HRef H B)).length ≤ (hp n m hn hm).len root .dyn),
      (overwriteSlice (hp n m hn hm) root .dyn 0 [neighbor] hd).index root .dyn zero = some neighbor ∧
      MObj.elems .dyn ((overwriteSlice (hp n m hn hm) root .dyn 0 [neighbor] hd).get root) =
        replaceSlice (List.replicate m child) 0 [neighbor] ∧
      overwriteIntervals (hp n m hn hm) root .dyn 0 [neighbor] hd 0 [child] he = hp n m hn hm := by
  have hlen : (hp n m hn hm).len root .dyn = m := by
    simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,root,List.length_replicate]
  have hd : 0+([neighbor] : List (HRef H B)).length ≤ (hp n m hn hm).len root .dyn := by
    rw [hlen]; simp only [List.length_cons,List.length_nil]; omega
  have he : 0+([child] : List (HRef H B)).length ≤ (hp n m hn hm).len root .dyn := hd
  refine ⟨hd,he,?_,?_,?_⟩
  · change (MObj.elems .dyn ((overwriteSlice (hp n m hn hm) root .dyn 0 [neighbor] hd).get root))[0]? = some neighbor
    exact overwriteSlice_inside _ root .dyn 0 0 [neighbor] hd (by decide)
  · rw [overwriteSlice_elems]; simp only [MObj.elems_dyn]; rfl
  · apply (overwriteIntervals_eq_self_iff _ root .dyn 0 [neighbor] hd 0 [child] he).mpr
    constructor
    · intro i hi
      have he : i = 0 := by change i < 1 at hi; omega
      subst i
      simp only [MObj.elems_dyn]
      change some child = (List.replicate m child)[0]?
      exact (List.getElem?_replicate_of_lt hm0).symm
    · intro i hi hx
      change i < 1 at hi
      change 0+i < 0 ∨ 0+1 ≤ 0+i at hx
      omega

/-- Concrete nonempty selections across element32 use the runtime theorem. -/
theorem selected_boundary :
    (out 33 33 (by decide) (by decide)).index root .dyn zero = some child ∧
    (out 33 33 (by decide) (by decide)).index root .dyn (⟨32,by decide⟩ : U) = some child ∧
    RefChildRepr (table 33 33) address (out 33 33 (by decide) (by decide)) rv root :=
  ⟨(typed_aliases 33 33 (by decide) (by decide) zero (by decide)).2.1,
   (typed_aliases 33 33 (by decide) (by decide) (⟨32,by decide⟩ : U) (by decide)).2.1,
   (represented 33 33 (by decide) (by decide)).2⟩

/-- The first operation really succeeds before each independently bad second
operation. These are Option observations only, with no rollback semantics. -/
theorem second_failure_stages (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    checkedCalldataBools (bools firstPayload) 7 (hp n m hn hm) child .dyn 0 2 0 = some (mid n m hn hm) ∧
    checkedCalldataBools (bools secondPayload) 8 (mid n m hn hm) child .dyn 0 2 1 = none ∧
    checkedCalldataBools (bools secondPayload) 7 (mid n m hn hm) child .dyn 2 1 1 = none ∧
    checkedCalldataBools (bools secondPayload) 7 (mid n m hn hm) child .dyn 0 3 0 = none ∧
    checkedCalldataBools (bools secondPayload) 7 (mid n m hn hm) child .dyn 0 2 (n+3) = none := by
  refine ⟨actual_single firstPayload _ 0 (cap1 n m hn hm),?_,?_,?_,?_⟩
  · exact checkedCalldataBools_no_payload _ _ _ _ _ _ _ _ rfl
  all_goals apply (boolTransfer_none_lookup _ _ _ _ _ _ _ _).mpr
  all_goals rw [calldataBools_lookup (bool_repr secondPayload),bool_values]
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inl (by decide))
  · apply Or.inr; apply Or.inr
    dsimp only [mid]
    rw [overwriteSlice_len]
    simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,child,old,
      List.length_append,List.length_cons,List.length_nil,List.length_replicate]
    omega

/-- Ordered sequence rejection preserves the successful reached first stage;
an independently missing first lookup still short-circuits the sequence. -/
theorem ordered_failures (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    checkedBoolSequence (bools firstPayload) 7 (bools secondPayload) 8 (hp n m hn hm)
      child .dyn 0 2 0 child .dyn 0 2 1 = none ∧
    checkedBoolSequence (bools firstPayload) 7 (bools secondPayload) 7 (hp n m hn hm)
      child .dyn 0 2 0 child .dyn 2 1 1 = none ∧
    checkedBoolSequence (bools firstPayload) 7 (bools secondPayload) 7 (hp n m hn hm)
      child .dyn 0 2 0 child .dyn 0 3 0 = none ∧
    checkedBoolSequence (bools firstPayload) 7 (bools secondPayload) 7 (hp n m hn hm)
      child .dyn 0 2 0 child .dyn 0 2 (n+3) = none ∧
    checkedBoolSequence (bools firstPayload) 8 (bools secondPayload) 7 (hp n m hn hm)
      child .dyn 0 2 0 child .dyn 0 2 1 = none := by
  obtain ⟨hf,hlookup,hreverse,hsource,hdestination⟩ := second_failure_stages n m hn hm
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (checkedBoolSequence_none_ordered _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr (Or.inr ⟨_,hf,hlookup⟩)
  · exact (checkedBoolSequence_none_ordered _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr (Or.inr ⟨_,hf,hreverse⟩)
  · exact (checkedBoolSequence_none_ordered _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr (Or.inr ⟨_,hf,hsource⟩)
  · exact (checkedBoolSequence_none_ordered _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr (Or.inr ⟨_,hf,hdestination⟩)
  · apply (checkedBoolSequence_none_ordered _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    exact Or.inl (checkedCalldataBools_no_payload _ _ _ _ _ _ _ _ rfl)

/-- The source-only test has valid destination capacity even at n0; the
reverse-only test has a valid source upper bound/capacity, and the destination-
only test has a fully valid source slice. All use the REAL reached length. -/
theorem isolated_guards (n m : Nat) (hn : n+3 < 2^256) (hm : m < 2^256) :
    (0 ≤ 3 ∧ secondPayload.length < 3 ∧ 0+(3-0) ≤ (mid n m hn hm).len child .dyn) ∧
    (1 ≤ secondPayload.length ∧ 1+(1-2) ≤ (mid n m hn hm).len child .dyn ∧ 1 < 2) ∧
    (SliceBounds secondPayload.length 0 2 ∧ (mid n m hn hm).len child .dyn < (n+3)+(2-0)) := by
  have hl : (mid n m hn hm).len child .dyn = n+3 := by
    dsimp only [mid]
    rw [overwriteSlice_len]
    simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,child,old,
      List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
  rw [hl]
  refine ⟨⟨by decide,by decide,by omega⟩,⟨by decide,by omega,by decide⟩,⟨⟨by decide,by decide⟩,by omega⟩⟩

/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.isolated_guards' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms isolated_guards
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.second_failure_stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms second_failure_stages
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.ordered_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered_failures
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms endpoints
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.reference_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_restore
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.selected_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_boundary
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.second_reached' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms second_reached
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.changed_final_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_final_negative
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.incomplete_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms incomplete_negative
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.wrong_order_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_order_negative
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.typed_aliases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms typed_aliases
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.criterion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms criterion
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.break_then_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms break_then_restore
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented
/-- info: 'Solidity.Backend.MemoryOps.RestorationControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms observations
end Solidity.Backend.MemoryOps.RestorationControls
