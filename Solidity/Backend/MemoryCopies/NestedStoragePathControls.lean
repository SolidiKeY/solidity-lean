import Solidity.Backend.MemoryCopies.NestedStoragePath
import Solidity.Evm.Correct

/-! Actual dynamic-outer path copy, declaration and rebinding preserve a
populated old parent/child graph and distinguish the selected local alias. -/
namespace Solidity.Backend.MemoryCopies.NestedStoragePathControls
open Evm Evm.Memory Semantics
private abbrev leaf : RefTy := .array (.prim .uint)
private abbrev parent : RefTy := .array (.ref leaf)
private def C : Contract := {vars := [("matrix",.ref (.array (.ref leaf)))]}
private def root : C.rootType "matrix" = some (.ref (.array (.ref leaf))) := by decide +kernel
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private def wide : 128 < W := by decide
private def array (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref leaf) :=
  .array (SVec.ofList ((values payloads).map SVal.prim))
    (.cons (.prim (indexValue (wmod 83))) .nil)
    (by rw [values,List.length_map,List.length_map]; exact Nat.lt_trans bounded wide)
private def matrix (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref (.array (.ref leaf))) :=
  .array (.cons (array payloads bounded) .nil)
    (.cons (array [] (by decide)) .nil) (by decide)
private abbrev H : HTy := [leaf,parent]
private abbrev Γ : Ctx := [.mem parent,.mem parent]
private def oldChild : HRef H leaf := ⟨0,rfl⟩
private def old : HRef H parent := ⟨1,rfl⟩
private def heap : Heap H := (⟨[indexValue (wmod 7)],by decide⟩,(⟨[oldChild],by decide⟩,()))
private def state (payloads : List (Fin W)) (bounded : payloads.length < 128) : State C Γ :=
  {storage := .cons (matrix payloads bounded) .nil,H := H,heap := heap,env := (some old,(some old,()))}
private def store (payloads : List (Fin W)) : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod 1
  | .data (.root 0) index => if index = 0 then wmod payloads.length else wmod 99
  | .data (.data (.root 0) _index) offset => payloads[offset]?.getD (wmod 83)
  | _ => wmod 0⟩
private def machine (cursor : Fin W) (payloads : List (Fin W)) : Machine :=
  {Machine.init with
    store := store payloads
    stack := [w[77]]
    mem := fun address => if address = 0 then .val cursor else if address = 1 ∨ address = 2 then w[16]
      else if address = 7 then w[99] else if address = 16 then w[1] else if address = 17 then w[18] else if address = 18 then w[1] else if address = 19 then w[7] else w[0]}
private def bases : Nat → Fin W := fun index => if index = 0 then wmod 18 else wmod 16
private def path : SPath C Γ (.ref (.array (.ref leaf))) := .loc (.root "matrix" root)
private def reference : SRef C (.ref (.array (.ref leaf))) := SRef.ofRoot "matrix" root
private def destination : Idx Γ (.mem parent) := .here
private theorem refs {R : RefTy} (reference : HRef H R) :
    (R = leaf ∧ HEq reference oldChild) ∨ (R = parent ∧ HEq reference old) := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact .inl ⟨rfl,HEq.rfl⟩
  | succ index => cases index with
    | zero => cases selected; exact .inr ⟨rfl,HEq.rfl⟩
    | succ index => cases selected

private theorem leaf_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprAt (store payloads) 128 (.ref leaf) (.data (.root 0) 0) (array payloads bounded) := by
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
  change (if name = "matrix" then some (.ref (.array (.ref leaf))) else none) = some type at found
  split at found
  · rename_i same
    subst name
    cases found
    change ReprAt (store payloads) 128 (.ref (.array (.ref leaf))) (.root 0) (matrix payloads bounded)
    refine .array rfl (by decide) ?_
    intro index item selected
    simp only [SVec.toList_cons,SVec.toList_nil] at selected
    cases index with
    | zero => cases selected; exact leaf_repr payloads bounded
    | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at selected; cases selected
  · cases found

private theorem core (cursor : Fin W) (payloads : List (Fin W)) (bounded : payloads.length < 128) : Sim C 128 1 (Frag.init Γ) (state payloads bounded) (machine cursor payloads) := by
  have initial : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) (Machine.init (fun _ => 0) ⟨0,W_pos⟩) :=
    Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨storage_repr payloads bounded,?_,?_,initial.net,initial.netSelf,by unfold Lmax; decide,?_,initial.env,initial.funds,initial.oracle⟩
  all_goals intro p index
  all_goals cases index with
    | there index => cases index with
      | there index => nomatch index

private theorem heap_repr (cursor : Fin W) (payloads : List (Fin W)) :
    Objects.HeapRepr heap bases 8 (machine cursor payloads) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro R reference
    rcases refs reference with ⟨rfl,equal⟩ | ⟨rfl,equal⟩ <;> cases equal <;> decide +kernel
  · intro R reference
    rcases refs reference with ⟨rfl,equal⟩ | ⟨rfl,equal⟩ <;> cases equal <;> decide +kernel
  · intro R Q left right different
    rcases refs left with ⟨rfl,leftEq⟩ | ⟨rfl,leftEq⟩ <;> cases leftEq
      <;> rcases refs right with ⟨rfl,rightEq⟩ | ⟨rfl,rightEq⟩ <;> cases rightEq
      <;> first | exact (different rfl).elim | decide +kernel
  · intro A E array reference
    rcases refs reference with ⟨rfl,equal⟩ | ⟨rfl,equal⟩
    · cases equal
      cases array
      refine ⟨by decide +kernel,?_,?_⟩
      · intro _; with_unfolding_all rfl
      · intro index item selected
        with_unfolding_all change ([indexValue (wmod 7)] : List PrimTy.uint.Denote)[index]? = some item at selected
        cases index with
        | zero => cases selected; exact ReprV.uint_of rfl
        | succ index => cases selected
    · cases equal
      cases array
      refine ⟨by decide +kernel,?_,?_⟩
      · intro _; with_unfolding_all rfl
      · intro index item selected
        with_unfolding_all change ([oldChild] : List (HRef H leaf))[index]? = some item at selected
        cases index with
        | zero => cases selected; with_unfolding_all rfl
        | succ index => cases selected
  · intro name reference
    rcases refs reference with ⟨different,_⟩ | ⟨different,_⟩ <;> cases different
  · intro name field R reference chosen
    rcases refs reference with ⟨different,_⟩ | ⟨different,_⟩ <;> cases different

private theorem represented (cursor : Fin W) (payloads : List (Fin W)) (bounded : payloads.length < 128) : Objects.StateRepr 128 1 8 (Frag.init Γ) (state payloads bounded) bases (machine cursor payloads) := by
  refine ⟨core cursor payloads bounded,heap_repr cursor payloads,?_,by decide⟩
  intro R index
  cases index with
  | here => exact ⟨old,rfl,rfl⟩
  | there index => cases index with
    | here => exact ⟨old,rfl,rfl⟩
    | there index => nomatch index

private theorem allocator (cursor : Fin W) (room : 20 ≤ cursor.val) (payloads : List (Fin W)) :
    Objects.AllocatorRepr heap bases 8 cursor (machine cursor payloads) := by
  refine ⟨heap_repr cursor payloads,⟨by decide,by omega,rfl,?_⟩,?_⟩
  · intro address above
    simp only [machine,if_neg (show address ≠ 0 by omega),
      if_neg (show ¬ (address = 1 ∨ address = 2) by omega),if_neg (show address ≠ 7 by omega),
      if_neg (show address ≠ 16 by omega),if_neg (show address ≠ 17 by omega),if_neg (show address ≠ 18 by omega),if_neg (show address ≠ 19 by omega)]
  · intro R reference
    rcases refs reference with ⟨rfl,equal⟩ | ⟨rfl,equal⟩ <;> cases equal
    · have bound : (bases oldChild.id).val + Objects.cells heap oldChild ≤ 20 := by decide +kernel
      exact Nat.le_trans bound room
    · have bound : (bases old.id).val + Objects.cells heap old ≤ 20 := by decide +kernel
      exact Nat.le_trans bound room

theorem populated_inputs : Objects.StateRepr 128 1 8 (Frag.init Γ)
    (state [wmod 11,wmod 23] (by decide)) bases (machine (wmod 40) [wmod 11,wmod 23]) ∧
    Objects.AllocatorRepr heap bases 8 (wmod 40) (machine (wmod 40) [wmod 11,wmod 23]) :=
  ⟨represented _ _ (by decide),allocator _ (by decide) _⟩

private theorem all_payloads (cursor : Fin W) (room : 20 ≤ cursor.val) (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (∃ fits, NestedStoragePathRebindResult 128 1 8 (Frag.init Γ) (state payloads bounded) bases cursor
      (machine cursor payloads) destination path (matrix payloads bounded) fits) ∨
    (¬ cursor.val + nestedStorageParentDemand (nestedStorageLiveRows (matrix payloads bounded)) < W ∧
      run (nestedStoragePathRebindCode 1 destination path) (machine cursor payloads) = .revert) := by
  exact nested_storage_path_rebind (state payloads bounded) bases cursor (machine cursor payloads) destination path reference
    (matrix payloads bounded) (represented cursor payloads bounded) (allocator cursor room payloads) (by decide)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

private theorem pair_demand : nestedStorageParentDemand
    (nestedStorageLiveRows (matrix [wmod 11,wmod 23] (by decide))) = 5 := by with_unfolding_all rfl

theorem rebind_separates_old_alias :
    let original := matrix [wmod 11,wmod 23] (by decide)
    let initial := state [wmod 11,wmod 23] (by decide)
    let grown := original.copyStToM initial.heap rfl
    let after := (initial.adopt grown).1.setLocal destination (some grown.val)
    ∃ base target,
      TRun.rebindMem destination (.copy path rfl) initial = .ok ⟨after,grown.ext⟩ ∧
      run (nestedStoragePathRebindCode 1 destination path) (machine (wmod 40) [wmod 11,wmod 23]) = .ok target 0 ∧
      Objects.StateRepr 128 1 8 (Frag.init Γ) after base target ∧
      Objects.AllocatorRepr grown.heap base 8 (wmod 45) target ∧
      target.mem 2 = w[40] ∧ target.mem 1 = w[16] ∧ target.mem 7 = w[99] ∧
      target.mem 16 = w[1] ∧ target.mem 17 = w[18] ∧ target.mem 18 = w[1] ∧ target.mem 19 = w[7] ∧
      Heap.Keeps grown.ext heap grown.heap ∧ (old.wk grown.ext).id < grown.val.id ∧
      MVal.copyMToSt grown.heap grown.val = original.strip := by
  rcases all_payloads (wmod 40) (by decide) [wmod 11,wmod 23] (by decide) with success | refusal
  · obtain ⟨fits,base,target,sourceRun,ran,post,allocated,extension,stack,root,localCell,below,keeps,fresh,contents⟩ := success
    have actual : Objects.AllocatorRepr
        ((matrix [wmod 11,wmod 23] (by decide)).copyStToM (state [wmod 11,wmod 23] (by decide)).heap rfl).heap
        base 8 (wmod 45) target := by simpa only [pair_demand] using allocated
    refine ⟨base,target,sourceRun,ran,post,actual,localCell,?_,?_,?_,?_,?_,?_,keeps,fresh old,contents⟩
    · exact (below 1 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 7 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 16 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 17 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 18 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 19 (by decide) (by decide) (by decide)).trans rfl
  · have fits : (wmod 40).val + nestedStorageParentDemand
        (nestedStorageLiveRows (matrix [wmod 11,wmod 23] (by decide))) < W := by rw [pair_demand]; decide
    exact (refusal.1 fits).elim

private def saturated : Fin W := ⟨W-1,by have positive : 0 < W := W_pos; omega⟩

theorem capacity_refusal_after_path :
    run (compileSPath 1 path) (machine saturated [wmod 11,wmod 23]) =
      .ok ((machine saturated [wmod 11,wmod 23]).push (.slot (.root 0))) 0 ∧
    run (nestedStoragePathRebindCode 1 destination path) (machine saturated [wmod 11,wmod 23]) = .revert := by
  refine ⟨?_,?_⟩
  · with_unfolding_all rfl
  · rcases all_payloads saturated (by with_unfolding_all decide) [wmod 11,wmod 23] (by decide) with success | refusal
    · obtain ⟨fits,_⟩ := success
      rw [pair_demand] at fits
      have impossible : ¬ saturated.val + 5 < W := by with_unfolding_all decide
      exact (impossible fits).elim
    · exact refusal.2

theorem empty_child_success : ∃ fits,
    NestedStoragePathRebindResult 128 1 8 (Frag.init Γ) (state [] (by decide)) bases (wmod 40)
      (machine (wmod 40) []) destination path (matrix [] (by decide)) fits := by
  rcases all_payloads (wmod 40) (by decide) [] (by decide) with success | refusal
  · exact success
  · have fits : (wmod 40).val + nestedStorageParentDemand (nestedStorageLiveRows (matrix [] (by decide))) < W := by
      with_unfolding_all decide
    exact (refusal.1 fits).elim

theorem long_child_success : ∃ fits,
    NestedStoragePathRebindResult 128 1 8 (Frag.init Γ)
      (state (List.replicate 64 (wmod 11)) (by rw [List.length_replicate]; decide)) bases (wmod 40)
      (machine (wmod 40) (List.replicate 64 (wmod 11))) destination path
      (matrix (List.replicate 64 (wmod 11)) (by rw [List.length_replicate]; decide)) fits := by
  rcases all_payloads (wmod 40) (by decide) (List.replicate 64 (wmod 11)) (by rw [List.length_replicate]; decide) with success | refusal
  · exact success
  · have fits : (wmod 40).val + nestedStorageParentDemand
        (nestedStorageLiveRows (matrix (List.replicate 64 (wmod 11)) (by rw [List.length_replicate]; decide))) < W := by
      with_unfolding_all decide
    exact (refusal.1 fits).elim

theorem path_copy_growth :
    let original := matrix [wmod 11,wmod 23] (by decide)
    let grown := original.copyStToM heap rfl
    ∃ base target,
      run (nestedStoragePathCode 1 path) (machine (wmod 40) [wmod 11,wmod 23]) = .ok (target.push w[40]) 0 ∧
      Objects.AllocatorRepr grown.heap base 8 (wmod 45) target ∧
      grown.heap.len grown.val .dyn = 1 ∧ heapWords grown.heap = heapWords heap + 5 := by
  rcases nested_storage_path_copy (state [wmod 11,wmod 23] (by decide)) bases (wmod 40)
      (machine (wmod 40) [wmod 11,wmod 23]) path reference (matrix [wmod 11,wmod 23] (by decide))
      (core _ _ (by decide)) (allocator _ (by decide) _) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) with success | refusal
  · obtain ⟨fits,base,target,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents,growth⟩ := success
    have actual : Objects.AllocatorRepr
        ((matrix [wmod 11,wmod 23] (by decide)).copyStToM heap rfl).heap base 8 (wmod 45) target := by
      simpa only [pair_demand] using allocated
    have rowsLength : (nestedStorageLiveRows (matrix [wmod 11,wmod 23] (by decide))).length = 1 := by
      simp only [nestedStorageLiveRows,matrix,SVal.view_array,List.length_map,SVec.length_toList]
    exact ⟨base,target,ran,actual,length.trans rowsLength,by simpa only [pair_demand] using growth⟩
  · have fits : (wmod 40).val + nestedStorageParentDemand (nestedStorageLiveRows (matrix [wmod 11,wmod 23] (by decide))) < W := by
      rw [pair_demand]; decide
    exact (refusal.1 fits).elim

private theorem declare_payloads (cursor : Fin W) (room : 20 ≤ cursor.val) (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (∃ fits, NestedStoragePathDeclareResult 128 1 8 (Frag.init Γ) (state payloads bounded) bases cursor
      (machine cursor payloads) path (matrix payloads bounded) fits) ∨
    (¬ cursor.val + nestedStorageParentDemand (nestedStorageLiveRows (matrix payloads bounded)) < W ∧
      run (nestedStoragePathDeclareCode 1 path) (machine cursor payloads) = .revert) := by
  exact nested_storage_path_declare (state payloads bounded) bases cursor (machine cursor payloads) path reference
    (matrix payloads bounded) (represented cursor payloads bounded) (allocator cursor room payloads) (by decide)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by decide)

theorem declare_preserves_aliases :
    let original := matrix [wmod 11,wmod 23] (by decide)
    let initial := state [wmod 11,wmod 23] (by decide)
    let grown := original.copyStToM initial.heap rfl
    let after := (initial.adopt grown).1.push (t := .mem parent) (some grown.val)
    ∃ base target,
      TRun.declMem parent (some (.copy path rfl)) rfl initial = .ok ⟨after,grown.ext⟩ ∧
      run (nestedStoragePathDeclareCode 1 path) (machine (wmod 40) [wmod 11,wmod 23]) = .ok target 0 ∧
      Objects.StateRepr 128 1 8 ((Frag.init Γ).push (.mem parent) .ok) after base target ∧
      Objects.AllocatorRepr grown.heap base 8 (wmod 45) target ∧
      target.mem 3 = w[40] ∧ target.mem 1 = w[16] ∧ target.mem 2 = w[16] ∧
      target.mem 16 = w[1] ∧ target.mem 17 = w[18] ∧ target.mem 19 = w[7] ∧ Heap.Keeps grown.ext heap grown.heap := by
  rcases declare_payloads (wmod 40) (by decide) [wmod 11,wmod 23] (by decide) with success | refusal
  · obtain ⟨fits,base,target,sourceRun,ran,post,allocated,extension,stack,root,localCell,below,keeps,contents⟩ := success
    have actual : Objects.AllocatorRepr
        ((matrix [wmod 11,wmod 23] (by decide)).copyStToM heap rfl).heap base 8 (wmod 45) target := by
      simpa only [pair_demand] using allocated
    refine ⟨base,target,sourceRun,ran,post,actual,localCell,?_,?_,?_,?_,?_,keeps⟩
    · exact (below 1 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 2 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 16 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 17 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 19 (by decide) (by decide) (by decide)).trans rfl
  · have fits : (wmod 40).val + nestedStorageParentDemand (nestedStorageLiveRows (matrix [wmod 11,wmod 23] (by decide))) < W := by
      rw [pair_demand]; decide
    exact (refusal.1 fits).elim

theorem declaration_capacity_refusal :
    run (nestedStoragePathDeclareCode 1 path) (machine saturated [wmod 11,wmod 23]) = .revert := by
  rcases declare_payloads saturated (by with_unfolding_all decide) [wmod 11,wmod 23] (by decide) with success | refusal
  · obtain ⟨fits,_⟩ := success
    rw [pair_demand] at fits
    have impossible : ¬ saturated.val + 5 < W := by with_unfolding_all decide
    exact (impossible fits).elim
  · exact refusal.2

/--
info: 'Solidity.Backend.MemoryCopies.NestedStoragePathControls.populated_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms populated_inputs
/--
info: 'Solidity.Backend.MemoryCopies.NestedStoragePathControls.rebind_separates_old_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rebind_separates_old_alias
/--
info: 'Solidity.Backend.MemoryCopies.NestedStoragePathControls.capacity_refusal_after_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms capacity_refusal_after_path
/--
info: 'Solidity.Backend.MemoryCopies.NestedStoragePathControls.empty_child_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_child_success
/--
info: 'Solidity.Backend.MemoryCopies.NestedStoragePathControls.long_child_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms long_child_success
/--
info: 'Solidity.Backend.MemoryCopies.NestedStoragePathControls.path_copy_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms path_copy_growth
/--
info: 'Solidity.Backend.MemoryCopies.NestedStoragePathControls.declare_preserves_aliases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms declare_preserves_aliases
/--
info: 'Solidity.Backend.MemoryCopies.NestedStoragePathControls.declaration_capacity_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms declaration_capacity_refusal
end Solidity.Backend.MemoryCopies.NestedStoragePathControls
