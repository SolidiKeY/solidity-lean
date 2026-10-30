import Solidity.Backend.MemoryOps.CalldataAgreementChildren
import Solidity.Backend.MemoryOps.CalldataSequenceFixtures

/-! Nonempty same-content aliases are real decoded transfers. Only initial old
Source entries are constructed; uint mutation is material and remains observed. -/
namespace Solidity.Backend.MemoryOps.AgreementControls
open SequenceFixtures
private abbrev B := BoolChildRef
private abbrev C := RefChildRef
private abbrev N : RefTy := .array (.prim .uint)
private abbrev H : HTy := [B,B,N,C]
private def neighbor : HRef H B := ⟨0,rfl⟩
private def held : HRef H B := ⟨1,rfl⟩
private def nr : HRef H N := ⟨2,rfl⟩
private def root : HRef H C := ⟨3,rfl⟩
private def address (i : Nat) := 100+i
private def oldValues : List Bool := [false,true,false]
private def nv : List U := [maximum,one]
private def sv : Source.Data D RefChildTy := .val (.cdRef rfl (address root.id))
private def leafSv : Source.Data D BoolChildTy := .val (.cdRef rfl (address held.id))
private def tables (n : Nat) : Source.Calldata D := ⟨[],fun off =>
  if off = 101 then some ⟨BoolChildTy,decodedBools oldValues⟩ else
  if off = 103 then some ⟨RefChildTy,decodedChildRefs address (List.replicate n held)⟩ else none⟩
private def heap (n : Nat) (hn : n < 2^256) : Heap H :=
  (⟨[true,false],by decide⟩,⟨oldValues,by decide⟩,
   ⟨[seven,zero,one,zero],by decide⟩,
   ⟨List.replicate n held,by simpa only [List.length_replicate] using hn⟩,())
private theorem leaf_initial (n : Nat) (hn : n < 2^256) : BoolChildRepr (tables n) address (heap n hn) leafSv held := by
  refine ⟨rfl,?_⟩
  simp only [MObj.elems_dyn]; rfl
private theorem root_initial (n : Nat) (hn : n < 2^256) : RefChildRepr (tables n) address (heap n hn) sv root := by
  refine ⟨rfl,?_,?_⟩
  · simp only [MObj.elems_dyn]; rfl
  · intro leaf hl
    have hm : leaf ∈ List.replicate n held := by simpa only [MObj.elems_dyn] using hl
    have he := (List.mem_replicate.mp hm).2
    subst leaf
    exact leaf_initial n hn
private theorem lookup (n : Nat) : DecodedArrayAt (n := none) (tables n) 101 oldValues.length
    (fun _ h => by cases h) (fun i => .val (.bool oldValues[i])) := rfl
private theorem hb (n : Nat) (hn : n < 2^256) : 1+([true] : List Bool).length ≤ (heap n hn).len held .dyn := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held]; decide
private theorem hu (n : Nat) (hn : n < 2^256) : 1+nv.length ≤ (heap n hn).len nr .dyn := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held,nr]; decide
private def mid (n : Nat) (hn : n < 2^256) := overwriteSlice (heap n hn) held .dyn 1 [true] (hb n hn)
private theorem first_reached (n : Nat) (hn : n < 2^256) :
    checkedCalldataBools (tables n) 101 (heap n hn) held .dyn 1 2 1 = some (mid n hn) := by
  have h := checkedCalldataBools_some (lookup n) (heap n hn) held .dyn 1 2 1
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held]; decide)
  simpa only [bool_values] using h
private theorem agrees (n : Nat) (hn : n < 2^256) : BoolTransferAgrees (tables n) 101 (heap n hn) held .dyn 1 2 1 :=
  (leaf_initial n hn).self_agrees 1 2
private theorem first_identity (n : Nat) (hn : n < 2^256) : mid n hn = heap n hn :=
  boolTransfer_eq_self_of_agrees (tables n) 101 (heap n hn) held .dyn 1 2 1 (mid n hn) (first_reached n hn) (agrees n hn)
private theorem first (n : Nat) (hn : n < 2^256) :
    checkedCalldataBools (tables n) 101 (heap n hn) held .dyn 1 2 1 = some (heap n hn) := by
  rw [first_reached,first_identity]
private def out (n : Nat) (hn : n < 2^256) := overwriteSlice (heap n hn) nr .dyn 1 nv (hu n hn)
private theorem run (n : Nat) (hn : n < 2^256) :
    checkedBoolUintSequence (tables n) 101 (uints nv) 9 (heap n hn) held .dyn 1 2 1 nr .dyn 0 2 1 = some (out n hn) := by
  unfold checkedBoolUintSequence
  rw [first]
  have h := checkedCalldataUints_some (uint_repr nv) (heap n hn) nr .dyn 0 2 1
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held,nr]; decide)
  simpa only [Option.bind_some,calldataUint_values] using h

theorem nonempty_alias (n : Nat) (hn : n < 2^256) :
    1 < (2 : Nat) ∧ checkedCalldataBools (tables n) 101 (heap n hn) held .dyn 1 2 1 = some (heap n hn) ∧
    checkedBoolUintSequence (tables n) 101 (uints nv) 9 (heap n hn) held .dyn 1 2 1 nr .dyn 0 2 1 = some (out n hn) ∧
    RefChildRepr (tables n) address (out n hn) sv root := by
  refine ⟨by decide,first n hn,run n hn,(root_initial n hn).mixedSequence_agrees (tables n) 101 (uints nv) 9 held .dyn 1 2 1 nr .dyn 0 2 1 (out n hn) (run n hn) ?_⟩
  intro leaf _
  right; right
  exact agrees n hn

private theorem reverse_run (n : Nat) (hn : n < 2^256) :
    checkedUintBoolSequence (uints nv) 9 (tables n) 101 (heap n hn) nr .dyn 0 2 1 held .dyn 1 2 1 = some (out n hn) := by
  have h := checkedBoolUintSequence_comm (lookup n) (uint_repr nv) (heap n hn) held .dyn 1 2 1 nr .dyn 0 2 1
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held,nr]; decide)
  exact h.symm.trans (run n hn)

theorem reverse_alias (n : Nat) (hn : n < 2^256) :
    checkedUintBoolSequence (uints nv) 9 (tables n) 101 (heap n hn) nr .dyn 0 2 1 held .dyn 1 2 1 = some (out n hn) ∧
    RefChildRepr (tables n) address (out n hn) sv root := by
  refine ⟨reverse_run n hn,(root_initial n hn).reverseMixedSequence_agrees (lookup n) (uint_repr nv) held .dyn 1 2 1 nr .dyn 0 2 1 (out n hn) (reverse_run n hn) ?_⟩
  intro leaf _
  right; right
  exact agrees n hn

private theorem held_frame (n : Nat) (hn : n < 2^256) : (out n hn).get held = (heap n hn).get held :=
  mixedTransfer_frame_agrees (tables n) 101 (uints nv) 9 (heap n hn) held .dyn 1 2 1 nr .dyn 0 2 1 (out n hn) (run n hn) held
    (Or.inr (Or.inr (agrees n hn))) (Or.inl (by decide))
private theorem root_frame (n : Nat) (hn : n < 2^256) : (out n hn).get root = (heap n hn).get root :=
  mixedTransfer_frame_agrees (tables n) 101 (uints nv) 9 (heap n hn) held .dyn 1 2 1 nr .dyn 0 2 1 (out n hn) (run n hn) root
    (Or.inl (by decide)) (Or.inl (by decide))

theorem full_observations (n : Nat) (hn : n < 2^256) :
    MObj.elems .dyn ((out n hn).get held) = [false,true,false] ∧
    MObj.elems .dyn ((out n hn).get neighbor) = [true,false] ∧
    (MObj.elems .dyn ((out n hn).get nr)).map (fun v : U => v.val) = [7,((2^256-1 : Nat) : Int),1,0] ∧
    (MObj.elems .dyn ((out n hn).get root)).map HRef.id = List.replicate n 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [held_frame]; simp only [MObj.elems_dyn]; rfl
  · rw [out,overwriteSlice_frame _ nr neighbor .dyn _ _ _ (by decide)]
    simp only [MObj.elems_dyn]; rfl
  · rw [out,overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl
  · rw [root_frame]
    simp only [MObj.elems_dyn]
    change (List.replicate n held).map HRef.id = List.replicate n 1
    rw [List.map_replicate]
    rfl

theorem typed_reads (n : Nat) (hn : n < 2^256) (i : U) (hi : i.val.toNat < n) :
    (out n hn).index root .dyn i = some held ∧
    (out n hn).index held .dyn zero = some false ∧
    (out n hn).index held .dyn one = some true ∧
    (out n hn).index held .dyn (⟨2,by decide⟩ : U) = some false := by
  refine ⟨?_,?_,?_,?_⟩
  · change (MObj.elems .dyn ((out n hn).get root))[i.val.toNat]? = some held
    rw [root_frame]; simp only [MObj.elems_dyn]
    exact List.getElem?_replicate_of_lt hi
  all_goals change (MObj.elems .dyn ((out n hn).get held))[_]? = _
  all_goals rw [held_frame]; simp only [MObj.elems_dyn]; rfl

theorem selected_and_boundary :
    RefChildRepr (tables 33) address (out 33 (by decide)) sv root ∧
    (out 33 (by decide)).index root .dyn zero = some held ∧
    (out 33 (by decide)).index root .dyn (⟨32,by decide⟩ : U) = some held :=
  ⟨(nonempty_alias 33 (by decide)).2.2.2,(typed_reads 33 (by decide) zero (by decide)).1,
    (typed_reads 33 (by decide) (⟨32,by decide⟩ : U) (by decide)).1⟩

/-- Reference-valued writes also use the generic pointwise whole-heap law. -/
theorem reference_identity (n : Nat) (hn : n < 2^256) :
    overwriteSlice (heap n hn) root .dyn 0 (MObj.elems .dyn ((heap n hn).get root))
      (by simp only [Heap.len,Nat.zero_add]; exact Nat.le_refl _) = heap n hn := by
  apply overwriteSlice_eq_self_of_agrees
  intro i _
  simp only [Nat.zero_add]

private def wrong : List Bool := [true,true,false]
private theorem hbad (n : Nat) (hn : n < 2^256) : 0+([true] : List Bool).length ≤ (heap n hn).len held .dyn := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held]; decide
private def bad (n : Nat) (hn : n < 2^256) := overwriteTwo (heap n hn) held .dyn 0 [true] (hbad n hn) nr .dyn 1 nv (hu n hn) (by decide)
private theorem bad_run (n : Nat) (hn : n < 2^256) :
    checkedBoolUintSequence (bools wrong) 7 (uints nv) 9 (heap n hn) held .dyn 0 1 0 nr .dyn 0 2 1 = some (bad n hn) := by
  have h := checkedBoolUintSequence_checked (bool_repr wrong) (uint_repr nv) (heap n hn) held .dyn 0 1 0 nr .dyn 0 2 1
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held,nr]; decide)
  simpa only [bool_values,calldataUint_values] using h
private theorem bad_child (n : Nat) (hn : n < 2^256) : MObj.elems .dyn ((bad n hn).get held) = [true,true,false] := by
  rw [bad,overwriteTwo_first,overwriteSlice_elems]
  simp only [MObj.elems_dyn]; rfl

theorem one_disagreement (n : Nat) (hn : n < 2^256) (hpos : 0 < n) :
    checkedBoolUintSequence (bools wrong) 7 (uints nv) 9 (heap n hn) held .dyn 0 1 0 nr .dyn 0 2 1 = some (bad n hn) ∧
    ¬ BoolTransferAgrees (bools wrong) 7 (heap n hn) held .dyn 0 1 0 ∧
    MObj.elems .dyn ((bad n hn).get held) = [true,true,false] ∧
    ¬ RefChildRepr (tables n) address (bad n hn) sv root := by
  refine ⟨bad_run n hn,?_,bad_child n hn,?_⟩
  · intro ha
    unfold BoolTransferAgrees at ha
    rw [calldataBools_lookup (bool_repr wrong),bool_values] at ha
    have h := ha 0 (by decide)
    simp only [MObj.elems_dyn] at h
    change (some true : Option Bool) = some false at h
    cases h
  · intro hr
    have hf : (bad n hn).get root = (heap n hn).get root :=
      mixedTransfer_frame_or_empty (bools wrong) 7 (uints nv) 9 (heap n hn) held .dyn 0 1 0 nr .dyn 0 2 1 (bad n hn) (bad_run n hn) root (Or.inl (by decide)) (Or.inl (by decide))
    have hm : held ∈ MObj.elems .dyn ((bad n hn).get root) := by
      rw [hf]; simp only [MObj.elems_dyn]
      exact List.mem_replicate.mpr ⟨by omega,rfl⟩
    have leaf := hr.2.2 held hm
    have hs : DecodedBoolRead (tables n) 101 0 true :=
      (leaf.read_iff 0 true).mpr (by rw [bad_child]; rfl)
    have hc : DecodedBoolArray (tables n) 101 oldValues := rfl
    have h := (decodedBoolRead_iff hc).mp hs
    change (some false : Option Bool) = some true at h
    cases h

theorem empty_root_case : RefChildRepr (tables 0) address (bad 0 (by decide)) sv root := by
  apply (root_initial 0 (by decide)).mixedSequence_agrees (bools wrong) 7 (uints nv) 9 held .dyn 0 1 0 nr .dyn 0 2 1 _ (bad_run 0 (by decide))
  intro leaf hl
  simp only [MObj.elems_dyn] at hl
  change leaf ∈ ([] : List (HRef H B)) at hl
  cases hl

/-- info: 'Solidity.Backend.MemoryOps.AgreementControls.nonempty_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nonempty_alias
/-- info: 'Solidity.Backend.MemoryOps.AgreementControls.reverse_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reverse_alias
/-- info: 'Solidity.Backend.MemoryOps.AgreementControls.full_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_observations
/-- info: 'Solidity.Backend.MemoryOps.AgreementControls.typed_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms typed_reads
/-- info: 'Solidity.Backend.MemoryOps.AgreementControls.selected_and_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_and_boundary
/-- info: 'Solidity.Backend.MemoryOps.AgreementControls.reference_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_identity
/-- info: 'Solidity.Backend.MemoryOps.AgreementControls.one_disagreement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms one_disagreement
/-- info: 'Solidity.Backend.MemoryOps.AgreementControls.empty_root_case' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_root_case
/-- The sequence is not a vacuous whole-heap identity: uint really changes. -/
theorem uint_changes (n : Nat) (hn : n < 2^256) : (out n hn).get nr ≠ (heap n hn).get nr := by
  intro he
  have h := congrArg (fun o : MObj H N => (MObj.elems .dyn o).map (fun v : U => v.val)) he
  dsimp only at h
  rw [(full_observations n hn).2.2.1] at h
  have old : (MObj.elems .dyn ((heap n hn).get nr)).map (fun v : U => v.val) = [7,0,1,0] := by
    simp only [MObj.elems_dyn]; rfl
  rw [old] at h
  exact (by decide : ([7,((2^256-1 : Nat) : Int),1,0] : List Int) ≠ [7,0,1,0]) h
/-- info: 'Solidity.Backend.MemoryOps.AgreementControls.uint_changes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uint_changes
/-- Published allocation discharges the prefix premise. Same-content alias
identity includes the new object, while the uint mutation and fresh reference
fields are observed. The existing Source table has NO entry for the new root. -/
theorem allocation_agreement (n : Nat) (hn : n < 2^256) :
    let obj : MObj H C := ⟨[held,held],by decide⟩
    let g := (heap n hn).alloc obj
    let e := List.prefix_append H [C]
    ∃ result,
      checkedCalldataBools (tables n) 101 g.1 (held.wk e) .dyn 1 2 1 = some g.1 ∧
      checkedBoolUintSequence (tables n) 101 (uints nv) 9 g.1 (held.wk e) .dyn 1 2 1 (nr.wk e) .dyn 0 2 1 = some result ∧
      (MObj.elems .dyn (result.get g.2)).map HRef.id = [1,1] ∧
      (MObj.elems .dyn (result.get (nr.wk e))).map (fun v : U => v.val) = [7,((2^256-1 : Nat) : Int),1,0] ∧
      (tables n).objects (address g.2.id) = none := by
  dsimp only
  let obj : MObj H C := ⟨[held,held],by decide⟩
  let g := (heap n hn).alloc obj
  let e := List.prefix_append H [C]
  have hk : Heap.Keeps e (heap n hn) g.1 := Heap.keeps_alloc (R := C) (heap n hn) obj
  have ha : BoolTransferAgrees (tables n) 101 g.1 (held.wk e) .dyn 1 2 1 :=
    (BoolTransferAgrees.keeps_iff (tables n) 101 e hk held .dyn 1 2 1).mpr (agrees n hn)
  obtain ⟨firstMid,hf,_⟩ := checkedCalldataBools_keeps (lookup n) e hk held .dyn 1 2 1 (heap n hn) (first n hn)
  have hi := boolTransfer_eq_self_of_agrees (tables n) 101 g.1 (held.wk e) .dyn 1 2 1 firstMid hf ha
  obtain ⟨result,ho,hko⟩ := checkedBoolUintSequence_keeps (lookup n) (uint_repr nv) e hk held .dyn 1 2 1 nr .dyn 0 2 1 (out n hn) (run n hn)
  have hframe : result.get g.2 = g.1.get g.2 := mixedTransfer_frame_agrees (tables n) 101 (uints nv) 9 g.1 (held.wk e) .dyn 1 2 1 (nr.wk e) .dyn 0 2 1 result ho g.2
    (Or.inr (Or.inr ha)) (Or.inl (by change (2 : Nat) ≠ 4; decide))
  refine ⟨result,hf.trans (congrArg some hi),ho,?_,?_,?_⟩
  · rw [hframe,Heap.get_alloc,MObj.elems_wk,List.map_map]
    simp only [MObj.elems_dyn]; rfl
  · rw [hko nr,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .uint)) (fun _ => rfl)]
    exact (full_observations n hn).2.2.1
  · change (tables n).objects 104 = none
    rfl
/-- info: 'Solidity.Backend.MemoryOps.AgreementControls.allocation_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms allocation_agreement
end Solidity.Backend.MemoryOps.AgreementControls
