import Solidity.Backend.MemoryCopies.FixedReferenceDeclare
import Solidity.Evm.Correct

/-! Nonempty contexts and heaps exercise existing local aliases, old object
contents, a sentinel and a real gap during checked fixed-reference copying. -/
namespace Solidity.Backend.MemoryCopies.FixedReferenceDeclareFrameControls
open Evm Evm.Memory Semantics
private abbrev leaf : RefTy := .array (.prim .uint)
private def C : Contract := {vars := [("matrix",.ref (.fixed (.ref leaf) 1))]}
private def root : C.rootType "matrix" = some (.ref (.fixed (.ref leaf) 1)) := by decide +kernel
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private def wide : 128 < W := by decide
private def array (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref leaf) :=
  .array (SVec.ofList ((values payloads).map SVal.prim))
    (.cons (.prim (indexValue (wmod 83))) .nil)
    (by rw [values,List.length_map,List.length_map]; exact Nat.lt_trans bounded wide)
private def matrix (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref (.fixed (.ref leaf) 1)) :=
  .fixed (.cons (array payloads bounded) .nil)
private abbrev H : HTy := [leaf]
private abbrev Γ : Ctx := [.mem leaf,.mem leaf]
private def old : HRef H leaf := ⟨0,rfl⟩
private def heap : Heap H := (⟨[indexValue (wmod 7)],by decide⟩,())
private def state (payloads : List (Fin W)) (bounded : payloads.length < 128) : State C Γ :=
  {storage := .cons (matrix payloads bounded) .nil,H := H,heap := heap,env := (some old,(some old,()))}
private def store (payloads : List (Fin W)) : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod payloads.length
  | .data (.root 0) index => payloads[index]?.getD (wmod 83)
  | _ => wmod 0⟩
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with
    store := store payloads
    stack := [w[77]]
    mem := fun address => if address = 0 then w[40] else if address = 1 ∨ address = 2 then w[16]
      else if address = 7 then w[99] else if address = 16 then w[1] else if address = 17 then w[7] else w[0]}
private def bases : Nat → Fin W := fun _ => wmod 16
private def path : SPath C Γ (.ref (.fixed (.ref leaf) 1)) := .loc (.root "matrix" root)
private def reference : SRef C (.ref (.fixed (.ref leaf) 1)) := SRef.ofRoot "matrix" root
private theorem refs {R : RefTy} (reference : HRef H R) : R = leaf ∧ HEq reference old := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact ⟨rfl,HEq.rfl⟩
  | succ index => cases selected

private theorem leaf_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprAt (store payloads) 128 (.ref leaf) (.root 0) (array payloads bounded) := by
  refine .array ?_ (by simpa only [values,List.length_map] using bounded) ?_
  · simp only [values,List.length_map]
    exact Nat.mod_eq_of_lt (Nat.lt_trans bounded wide)
  · intro index item selected
    simp only [SVec.toList_ofList,values,List.getElem?_map] at selected
    cases chosen : payloads[index]? with
    | none => simp only [chosen,Option.map_none] at selected; cases selected
    | some payload =>
      simp only [chosen,Option.map_some] at selected
      cases selected
      simp only [size_prim,Nat.mul_one]
      refine .prim (ReprV.uint_of ?_)
      simp only [store,chosen,Option.getD_some]
      rfl

private theorem storage_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprStore C 128 (store payloads) (state payloads bounded).storage := by
  intro name type found
  change (if name = "matrix" then some (.ref (.fixed (.ref leaf) 1)) else none) = some type at found
  split at found
  · rename_i same
    subst name
    cases found
    change ReprAt (store payloads) 128 (.ref (.fixed (.ref leaf) 1)) (.root 0) (matrix payloads bounded)
    refine .fixed ?_
    intro index item selected
    simp only [SVec.toList_cons,SVec.toList_nil] at selected
    cases index with
    | zero => cases selected; exact leaf_repr payloads bounded
    | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at selected; cases selected
  · cases found

private theorem core (payloads : List (Fin W)) (bounded : payloads.length < 128) : Sim C 128 1 (Frag.init Γ) (state payloads bounded) (machine payloads) := by
  have initial : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) (Machine.init (fun _ => 0) ⟨0,W_pos⟩) :=
    Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨storage_repr payloads bounded,?_,?_,initial.net,initial.netSelf,by unfold Lmax; decide,?_,initial.env,initial.funds,initial.oracle⟩
  all_goals intro p index
  all_goals cases index with
    | there index => cases index with
      | there index => nomatch index

private theorem heap_repr (payloads : List (Fin W)) : Objects.HeapRepr heap bases 8 (machine payloads) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro R reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    decide +kernel
  · intro R reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    decide +kernel
  · intro R Q left right different
    obtain ⟨rfl,leftEq⟩ := refs left
    obtain ⟨rfl,rightEq⟩ := refs right
    cases leftEq
    cases rightEq
    exact (different rfl).elim
  · intro A E array reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    cases array
    refine ⟨?_,?_,?_⟩
    · with_unfolding_all change 16 + 2 ≤ W
      decide
    · intro _
      with_unfolding_all rfl
    · intro index item selected
      with_unfolding_all change ([indexValue (wmod 7)] : List PrimTy.uint.Denote)[index]? = some item at selected
      cases index with
      | zero => cases selected; exact ReprV.uint_of rfl
      | succ index => cases selected
  · intro name reference
    obtain ⟨different,_⟩ := refs reference
    cases different
  · intro name field R reference fieldType
    obtain ⟨different,_⟩ := refs reference
    cases different

private theorem represented (payloads : List (Fin W)) (bounded : payloads.length < 128) : Objects.StateRepr 128 1 8 (Frag.init Γ) (state payloads bounded) bases (machine payloads) := by
  refine ⟨core payloads bounded,heap_repr payloads,?_,by decide⟩
  intro R index
  cases index with
  | here => exact ⟨old,rfl,rfl⟩
  | there index => cases index with
    | here => exact ⟨old,rfl,rfl⟩
    | there index => nomatch index

private theorem allocator (payloads : List (Fin W)) : Objects.AllocatorRepr heap bases 8 (wmod 40) (machine payloads) := by
  refine ⟨heap_repr payloads,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro address above
    change 40 ≤ address at above
    simp only [machine,if_neg (show address ≠ 0 by omega),
      if_neg (show ¬ (address = 1 ∨ address = 2) by omega),if_neg (show address ≠ 7 by omega),
      if_neg (show address ≠ 16 by omega),if_neg (show address ≠ 17 by omega)]
  · intro R reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    decide +kernel

private theorem old_gap : Objects.Gap heap bases 20 30 := by
  intro R reference
  obtain ⟨rfl,equal⟩ := refs reference
  cases equal
  left
  decide +kernel

private theorem pair_demand : fixedReferenceStorageParentDemand
    (fixedReferenceLiveRows (matrix [wmod 11,wmod 23] (by decide))) = 4 := by with_unfolding_all rfl

theorem nonempty_inputs : Objects.StateRepr 128 1 8 (Frag.init Γ)
    (state [wmod 11,wmod 23] (by decide)) bases (machine [wmod 11,wmod 23]) ∧
    Objects.AllocatorRepr heap bases 8 (wmod 40) (machine [wmod 11,wmod 23]) ∧
    Objects.Gap heap bases 20 30 := ⟨represented _ (by decide),allocator _,old_gap⟩

theorem declaration_preserves_live_frame :
    let original := matrix [wmod 11,wmod 23] (by decide)
    let initial := state [wmod 11,wmod 23] (by decide)
    let grown := original.copyStToM initial.heap rfl
    let after := (initial.adopt grown).1.push (t := .mem (.fixed (.ref leaf) 1)) (some grown.val)
    ∃ base target,
      run (fixedReferenceDeclareCode 1 path) (machine [wmod 11,wmod 23]) = .ok target 0 ∧
      Objects.StateRepr 128 1 8 ((Frag.init Γ).push (.mem (.fixed (.ref leaf) 1)) .ok) after base target ∧
      Objects.AllocatorRepr grown.heap base 8 (wmod 44) target ∧
      target.mem 3 = w[40] ∧ target.mem 1 = w[16] ∧ target.mem 2 = w[16] ∧
      target.mem 7 = w[99] ∧ target.mem 16 = w[1] ∧ target.mem 17 = w[7] ∧
      Heap.Keeps grown.ext heap grown.heap ∧ MVal.copyMToSt grown.heap grown.val = original.strip := by
  rcases fixed_reference_declare_correct (state [wmod 11,wmod 23] (by decide)) bases (wmod 40)
      (machine [wmod 11,wmod 23]) path reference (matrix [wmod 11,wmod 23] (by decide))
      (represented _ (by decide)) (allocator _) (by decide) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by decide) with success | refusal
  · obtain ⟨fits,base,target,sourceRun,ran,post,allocated,extension,stack,root,localCell,below,keeps,contents⟩ := success
    have actual : Objects.AllocatorRepr
        ((matrix [wmod 11,wmod 23] (by decide)).copyStToM (state [wmod 11,wmod 23] (by decide)).heap rfl).heap
        base 8 (wmod 44) target := by simpa only [pair_demand] using allocated
    refine ⟨base,target,ran,post,actual,localCell,?_,?_,?_,?_,?_,keeps,contents⟩
    · exact (below 1 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 2 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 7 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 16 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 17 (by decide) (by decide) (by decide)).trans rfl
  · have fits : (wmod 40).val + fixedReferenceStorageParentDemand
        (fixedReferenceLiveRows (matrix [wmod 11,wmod 23] (by decide))) < W := by rw [pair_demand]; decide
    exact (refusal.1 fits).elim

theorem copy_preserves_inhabited_gap :
    let original := matrix [wmod 11,wmod 23] (by decide)
    let grown := original.copyStToM heap rfl
    ∃ base target,
      run (fixedReferencePathCopyCode 1 path) (machine [wmod 11,wmod 23]) = .ok (target.push w[40]) 0 ∧
      Objects.AllocatorRepr grown.heap base 8 (wmod 44) target ∧
      Objects.Gap grown.heap base 20 30 ∧ Heap.Keeps grown.ext heap grown.heap := by
  rcases fixed_reference_path_copy_correct (state [wmod 11,wmod 23] (by decide)) bases (wmod 40)
      (machine [wmod 11,wmod 23]) path reference (matrix [wmod 11,wmod 23] (by decide))
      (core _ (by decide)) (allocator _) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) with success | refusal
  · obtain ⟨fits,base,target,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents,growth⟩ := success
    have actual : Objects.AllocatorRepr
        ((matrix [wmod 11,wmod 23] (by decide)).copyStToM heap rfl).heap base 8 (wmod 44) target := by
      simpa only [pair_demand] using allocated
    exact ⟨base,target,ran,actual,gaps 20 30 old_gap (by decide),keeps⟩
  · have fits : (wmod 40).val + fixedReferenceStorageParentDemand
        (fixedReferenceLiveRows (matrix [wmod 11,wmod 23] (by decide))) < W := by rw [pair_demand]; decide
    exact (refusal.1 fits).elim

theorem old_object_overlaps_gap_refuted : ¬ Objects.Gap heap bases 17 18 := by
  intro gap
  rcases gap old with left | right
  · have impossible : ¬ ((bases old.id).val + Objects.cells heap old ≤ 17) := by decide +kernel
    exact impossible left
  · have impossible : ¬ (18 ≤ (bases old.id).val) := by decide +kernel
    exact impossible right

/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceDeclareFrameControls.nonempty_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nonempty_inputs
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceDeclareFrameControls.declaration_preserves_live_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms declaration_preserves_live_frame
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceDeclareFrameControls.copy_preserves_inhabited_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms copy_preserves_inhabited_gap
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceDeclareFrameControls.old_object_overlaps_gap_refuted' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms old_object_overlaps_gap_refuted
end Solidity.Backend.MemoryCopies.FixedReferenceDeclareFrameControls
