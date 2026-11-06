import Solidity.Backend.MemoryCopies.FixedReferencePathCopy
import Solidity.Evm.Correct

/-! Actual compiled path plus checked parent copying from retained-shadow
storage, with an original copied-heap allocator and a capacity refusal. -/
namespace Solidity.Backend.MemoryCopies.FixedReferencePathCopyControls
open Evm Evm.Memory Semantics
private abbrev Child : RefTy := .array (.prim .uint)
private abbrev Parent : RefTy := .fixed (.ref Child) 1
private def C : Contract := {vars := [("parent",.ref Parent)]}
private theorem root : C.rootType "parent" = some (.ref Parent) := by decide +kernel
private def shadow : SList (.prim .uint) := .cons (.prim (indexValue (wmod 83))) .nil
private def child (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref Child) :=
  .array (SVec.ofList (payloads.map (fun word => .prim (indexValue word)))) shadow
    (by rw [List.length_map]; exact Nat.lt_trans bounded (by decide))
private def value (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref Parent) :=
  .fixed (.cons (child payloads bounded) .nil)
private def state (payloads : List (Fin W)) (bounded : payloads.length < 128) : State C [] :=
  { (freshT C 0 W_pos ⟨0,W_pos⟩) with storage := .cons (value payloads bounded) .nil }
private def store (payloads : List (Fin W)) : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod payloads.length
  | .data (.root 0) index => payloads[index]?.getD (wmod 83)
  | _ => wmod 0⟩
private def machine (cursor : Fin W) (payloads : List (Fin W)) : Machine :=
  {Machine.init with
    store := store payloads
    stack := [w[77]]
    mem := fun address => if address = 0 then .val cursor else w[0]}
private def path : SPath C [] (.ref Parent) := .loc (.root "parent" root)
private def reference : SRef C (.ref Parent) := SRef.ofRoot "parent" root

private theorem child_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprAt (store payloads) 128 (.ref Child) (.root 0) (child payloads bounded) := by
  refine .array ?_ (by simpa only [List.length_map] using bounded) ?_
  · simp only [List.length_map]
    exact Nat.mod_eq_of_lt (Nat.lt_trans bounded (by decide))
  · intro index item selected
    simp only [SVec.toList_ofList,List.getElem?_map] at selected
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
  change (if name = "parent" then some (.ref Parent) else none) = some type at found
  split at found
  · rename_i same
    subst name
    cases found
    change ReprAt (store payloads) 128 (.ref Parent) (.root 0) (value payloads bounded)
    refine .fixed ?_
    intro index item selected
    simp only [SVec.toList_cons,SVec.toList_nil] at selected
    cases index with
    | zero => cases selected; exact child_repr payloads bounded
    | succ index => cases selected
  · cases found

private theorem represented (cursor : Fin W) (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Sim C 128 1 (Frag.init []) (state payloads bounded) (machine cursor payloads) := by
  have initial : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) (Machine.init (fun _ => 0) ⟨0,W_pos⟩) :=
    Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨storage_repr payloads bounded,?_,?_,initial.net,initial.netSelf,by unfold Lmax; decide,?_,initial.env,initial.funds,initial.oracle⟩
  all_goals intro p index; nomatch index

private def bases : Nat → Fin W := fun _ => wmod 0
private theorem allocator (cursor : Fin W) (above : 8 ≤ cursor.val) (payloads : List (Fin W)) :
    Objects.AllocatorRepr (Heap.empty : Heap []) bases 8 cursor (machine cursor payloads) := by
  refine ⟨⟨⟨?_,?_,?_⟩,?_,?_,?_⟩,⟨by decide,above,rfl,?_⟩,?_⟩
  · intro R reference; cases reference with | mk index chosen => cases index <;> cases chosen
  · intro R reference; cases reference with | mk index chosen => cases index <;> cases chosen
  · intro R Q left right different; cases left with | mk index chosen => cases index <;> cases chosen
  · intro A E array reference; cases reference with | mk index chosen => cases index <;> cases chosen
  · intro name reference; cases reference with | mk index chosen => cases index <;> cases chosen
  · intro name field R reference chosen; cases reference with | mk index selected => cases index <;> cases selected
  · intro address lower
    have nonzero : address ≠ 0 := by omega
    simp only [machine,if_neg nonzero]
  · intro R reference; cases reference with | mk index chosen => cases index <;> cases chosen

theorem certificate_inhabited : FixedReferencePathCopyCertificate := fixedReferencePathCopy

theorem all_fitting_payloads (cursor : Fin W) (above : 8 ≤ cursor.val) (payloads : List (Fin W))
    (bounded : payloads.length < 128) :
    (∃ fits, FixedReferencePathCopyResult 1 8 (state payloads bounded) bases cursor (machine cursor payloads)
      path (value payloads bounded) fits) ∨
    (¬ cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows (value payloads bounded)) < W ∧
      run (fixedReferencePathCopyCode 1 path) (machine cursor payloads) = .revert) := by
  exact fixed_reference_path_copy_correct (state payloads bounded) bases cursor (machine cursor payloads)
    path reference (value payloads bounded) (represented cursor payloads bounded) (allocator cursor above payloads)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

private theorem two_demand : fixedReferenceStorageParentDemand
    (fixedReferenceLiveRows (value [wmod 11,wmod 23] (by decide))) = 4 := by with_unfolding_all rfl

theorem actual_shadow_copy :
    let original := value [wmod 11,wmod 23] (by decide)
    let grown := original.copyStToM (state [wmod 11,wmod 23] (by decide)).heap rfl
    ∃ base target,
      run (fixedReferencePathCopyCode 1 path) (machine (wmod 40) [wmod 11,wmod 23]) = .ok (target.push w[40]) 0 ∧
      Objects.AllocatorRepr grown.heap base 8 (wmod 44) target ∧ base grown.val.id = wmod 40 ∧
      MVal.copyMToSt grown.heap grown.val = original.strip ∧ target.mem 0 = w[44] ∧ target.mem 44 = w[0] ∧
      target.stack = [w[77]] ∧ target.store.cells (.data (.root 0) 2) = wmod 83 := by
  rcases all_fitting_payloads (wmod 40) (by decide) [wmod 11,wmod 23] (by decide) with success | refusal
  · obtain ⟨fits,base,target,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents,growth⟩ := success
    have actual : Objects.AllocatorRepr
        ((value [wmod 11,wmod 23] (by decide)).copyStToM (state [wmod 11,wmod 23] (by decide)).heap rfl).heap
        base 8 (wmod 44) target := by
      simpa only [two_demand] using allocated
    refine ⟨base,target,ran,actual,root,contents,actual.free.cell,actual.free.zero 44 (by decide),?_,?_⟩
    · rw [shape]
      rfl
    · rw [shape]
      rfl
  · have fits : (wmod 40).val + fixedReferenceStorageParentDemand
        (fixedReferenceLiveRows (value [wmod 11,wmod 23] (by decide))) < W := by rw [two_demand]; decide
    exact (refusal.1 fits).elim

private def saturated : Fin W := ⟨W-1,by have positive : 0 < W := W_pos; omega⟩

theorem capacity_refusal_after_path :
    run (compileSPath 1 path) (machine saturated [wmod 11,wmod 23]) =
      .ok ((machine saturated [wmod 11,wmod 23]).push (.slot (.root 0))) 0 ∧
    run (fixedReferencePathCopyCode 1 path) (machine saturated [wmod 11,wmod 23]) = .revert := by
  refine ⟨?_,?_⟩
  · with_unfolding_all rfl
  · rcases all_fitting_payloads saturated (by with_unfolding_all decide) [wmod 11,wmod 23] (by decide) with success | refusal
    · obtain ⟨fits,_⟩ := success
      rw [two_demand] at fits
      have impossible : ¬ saturated.val + 4 < W := by with_unfolding_all decide
      exact (impossible fits).elim
    · exact refusal.2

theorem empty_child_success : ∃ fits,
    FixedReferencePathCopyResult 1 8 (state [] (by decide)) bases (wmod 40) (machine (wmod 40) []) path (value [] (by decide)) fits := by
  rcases all_fitting_payloads (wmod 40) (by decide) [] (by decide) with success | refusal
  · exact success
  · have fits : (wmod 40).val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows (value [] (by decide))) < W := by
      with_unfolding_all decide
    exact (refusal.1 fits).elim

theorem long_child_success : ∃ fits,
    FixedReferencePathCopyResult 1 8 (state (List.replicate 64 (wmod 11)) (by rw [List.length_replicate]; decide)) bases
      (wmod 40) (machine (wmod 40) (List.replicate 64 (wmod 11))) path
      (value (List.replicate 64 (wmod 11)) (by rw [List.length_replicate]; decide)) fits := by
  rcases all_fitting_payloads (wmod 40) (by decide) (List.replicate 64 (wmod 11)) (by rw [List.length_replicate]; decide) with success | refusal
  · exact success
  · have fits : (wmod 40).val + fixedReferenceStorageParentDemand
        (fixedReferenceLiveRows (value (List.replicate 64 (wmod 11)) (by rw [List.length_replicate]; decide))) < W := by
      with_unfolding_all decide
    exact (refusal.1 fits).elim

/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathCopyControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathCopyControls.all_fitting_payloads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms all_fitting_payloads
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathCopyControls.actual_shadow_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_shadow_copy
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathCopyControls.capacity_refusal_after_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms capacity_refusal_after_path
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathCopyControls.empty_child_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_child_success
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathCopyControls.long_child_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms long_child_success
end Solidity.Backend.MemoryCopies.FixedReferencePathCopyControls
