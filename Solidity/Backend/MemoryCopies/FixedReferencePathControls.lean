import Solidity.Backend.MemoryCopies.FixedReferencePath
import Solidity.Evm.Correct

/-! Inhabited actual compiled root selection for live/empty/long children with
retained shadows. These controls test selection, not parent-copy execution. -/
namespace Solidity.Backend.MemoryCopies.FixedReferencePathControls
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
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with store := store payloads, stack := [w[77]]}
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

private theorem represented (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Sim C 128 1 (Frag.init []) (state payloads bounded) (machine payloads) := by
  have initial : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) (Machine.init (fun _ => 0) ⟨0,W_pos⟩) :=
    Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨storage_repr payloads bounded,?_,?_,initial.net,initial.netSelf,by unfold Lmax; decide,?_,initial.env,initial.funds,initial.oracle⟩
  all_goals intro p index; nomatch index

theorem certificate_inhabited : FixedReferencePathCertificate := fixedReferencePath

theorem actual_selection (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    FixedReferencePathResult 128 1 (machine payloads) path (value payloads bounded) := by
  exact fixed_reference_path_select (state payloads bounded) (machine payloads) path reference (value payloads bounded)
    (represented payloads bounded) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)

theorem empty_selection : FixedReferencePathResult 128 1 (machine []) path (value [] (by decide)) :=
  actual_selection [] (by decide)

theorem long_selection : FixedReferencePathResult 128 1 (machine (List.replicate 64 (wmod 11))) path
    (value (List.replicate 64 (wmod 11)) (by rw [List.length_replicate]; decide)) :=
  actual_selection _ (by rw [List.length_replicate]; decide)

theorem actual_prefix : run (compileSPath 1 path) (machine [wmod 11,wmod 23]) =
    .ok ((machine [wmod 11,wmod 23]).push (.slot (.root 0))) 0 := by with_unfolding_all rfl

theorem wrong_slot_refuted : run (compileSPath 1 path) (machine []) ≠
    .ok ((machine []).push (.slot (.data (.root 0) 0))) 0 := by
  intro same
  have actual : run (compileSPath 1 path) (machine []) = .ok ((machine []).push (.slot (.root 0))) 0 := by
    with_unfolding_all rfl
  rw [actual] at same
  cases same

/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathControls.actual_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_selection
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathControls.empty_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_selection
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathControls.long_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms long_selection
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathControls.actual_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_prefix
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferencePathControls.wrong_slot_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_slot_refuted
end Solidity.Backend.MemoryCopies.FixedReferencePathControls
