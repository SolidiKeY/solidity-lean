import Solidity.Backend.MemoryCopies.NestedMemoryPath
import Solidity.Backend.MemoryCopies.NestedMemoryPathFrame
import Solidity.Evm.Correct

/-! The source local is also the destination, and two old parent entries share
one child. Actual alias binding keeps identity; selected deep copying clones
both children while retaining the old graph and other local alias. -/
namespace Solidity.Backend.MemoryCopies.NestedMemoryPathControls
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
private def heap : Heap H := (⟨[indexValue (wmod 11),indexValue (wmod 23)],by decide⟩,(⟨[oldChild,oldChild],by decide⟩,()))
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
      else if address = 7 then w[99] else if address = 16 then w[2] else if address = 17 ∨ address = 18 then w[20]
      else if address = 20 then w[2] else if address = 21 then w[11] else if address = 22 then w[23] else w[0]}
private def bases : Nat → Fin W := fun index => if index = 0 then wmod 20 else wmod 16
private def destination : Idx Γ (.mem parent) := .here
private def path : MPath C Γ (.ref parent) := .var destination rfl
private def chosen : SelectedAlias 1 (Frag.init Γ) path := selectedAlias 1 (Frag.init Γ) path rfl
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
        with_unfolding_all change ([indexValue (wmod 11),indexValue (wmod 23)] : List PrimTy.uint.Denote)[index]? = some item at selected
        cases index with
        | zero => cases selected; exact ReprV.uint_of rfl
        | succ index => cases index with
          | zero => cases selected; exact ReprV.uint_of rfl
          | succ index => cases selected
    · cases equal
      cases array
      refine ⟨by decide +kernel,?_,?_⟩
      · intro _; with_unfolding_all rfl
      · intro index item selected
        with_unfolding_all change ([oldChild,oldChild] : List (HRef H leaf))[index]? = some item at selected
        cases index with
        | zero => cases selected; with_unfolding_all rfl
        | succ index => cases index with
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

private theorem allocator (cursor : Fin W) (room : 23 ≤ cursor.val) (payloads : List (Fin W)) :
    Objects.AllocatorRepr heap bases 8 cursor (machine cursor payloads) := by
  refine ⟨heap_repr cursor payloads,⟨by decide,by omega,rfl,?_⟩,?_⟩
  · intro address above
    simp only [machine,if_neg (show address ≠ 0 by omega),
      if_neg (show ¬ (address = 1 ∨ address = 2) by omega),if_neg (show address ≠ 7 by omega),
      if_neg (show address ≠ 16 by omega),if_neg (show ¬ (address = 17 ∨ address = 18) by omega),
      if_neg (show address ≠ 20 by omega),if_neg (show address ≠ 21 by omega),if_neg (show address ≠ 22 by omega)]
  · intro R reference
    rcases refs reference with ⟨rfl,equal⟩ | ⟨rfl,equal⟩ <;> cases equal
    · have bound : (bases oldChild.id).val + Objects.cells heap oldChild ≤ 23 := by decide +kernel
      exact Nat.le_trans bound room
    · have bound : (bases old.id).val + Objects.cells heap old ≤ 23 := by decide +kernel
      exact Nat.le_trans bound room

private def before : State C Γ := state [wmod 11,wmod 23] (by decide)
private def initial (cursor : Fin W) : Machine := machine cursor [wmod 11,wmod 23]
private def snapshot : SVal (.ref parent) := MVal.copyMToSt heap (T := .ref parent) old
private def grown := snapshot.copyStToM heap rfl
private theorem resolved : path.mvalT before = .ok old := by with_unfolding_all rfl
private theorem demand : memoryParentDemand heap .uint old = 9 := by with_unfolding_all rfl

theorem populated_inputs : Objects.StateRepr 128 1 8 (Frag.init Γ) before bases (initial (wmod 40)) ∧
    Objects.AllocatorRepr heap bases 8 (wmod 40) (initial (wmod 40)) :=
  ⟨represented _ _ (by decide),allocator _ (by decide) _⟩

theorem old_child_is_shared :
    (MObj.elems .dyn (heap.get old)).map (fun reference => reference.id) = [0,0] := by with_unfolding_all rfl

theorem copied_children_are_distinct :
    (MObj.elems .dyn (grown.heap.get grown.val)).map (fun reference => reference.id) = [2,3] := by
  with_unfolding_all rfl

theorem actual_deep_bind :
    let after := (before.adopt grown).1.setLocal destination (some grown.val)
    ∃ base target,
      run (chosen.nestedDeepBindCode destination) (initial (wmod 40)) = .ok target 0 ∧
      Objects.StateRepr 128 1 8 (Frag.init Γ) after base target ∧
      Objects.AllocatorRepr grown.heap base 8 (wmod 49) target ∧
      target.mem 2 = w[40] ∧ target.mem 1 = w[16] ∧ target.mem 7 = w[99] ∧
      target.mem 16 = w[2] ∧ target.mem 17 = w[20] ∧ target.mem 18 = w[20] ∧
      target.mem 20 = w[2] ∧ target.mem 21 = w[11] ∧ target.mem 22 = w[23] ∧
      Heap.Keeps grown.ext heap grown.heap ∧ old.id < grown.val.id ∧
      MVal.copyMToSt grown.heap grown.val = snapshot.strip ∧
      MVal.copyMToSt grown.heap (T := .ref parent) (old.wk grown.ext) = snapshot := by
  rcases chosen.nestedDeepBindExecute before bases (wmod 40) (initial (wmod 40)) destination
      (represented _ _ (by decide)) (allocator _ (by decide) _) (by decide) with success | refusal
  · obtain ⟨reference,resolution,fits,base,target,ran,post,allocated,root,extension,stack,localCell,below,keeps,fresh,newContents,oldContents⟩ := success
    rw [resolved] at resolution
    cases resolution
    have actual : Objects.AllocatorRepr grown.heap base 8 (wmod 49) target := by
      simpa only [before,state,grown,snapshot,demand] using allocated
    refine ⟨base,target,ran,post,actual,localCell,?_,?_,?_,?_,?_,?_,?_,?_,keeps,fresh,newContents,oldContents⟩
    · exact (below 1 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 7 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 16 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 17 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 18 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 20 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 21 (by decide) (by decide) (by decide)).trans rfl
    · exact (below 22 (by decide) (by decide) (by decide)).trans rfl
  · rcases refusal with ⟨refused,_⟩ | ⟨reference,resolution,tooLarge,_⟩
    · rw [resolved] at refused; cases refused
    · rw [resolved] at resolution; cases resolution
      have fits : (wmod 40).val + memoryParentDemand heap .uint old < W := by rw [demand]; decide
      exact (tooLarge fits).elim

private theorem old_gap : Objects.Gap heap bases 24 40 := by
  intro R reference
  rcases refs reference with ⟨rfl,equal⟩ | ⟨rfl,equal⟩
  · cases equal; left; decide +kernel
  · cases equal; left; decide +kernel

theorem deep_bind_preserves_inhabited_gap :
    Objects.Gap heap bases 24 40 ∧
    ∃ base target,
      run (chosen.nestedDeepBindCode destination) (initial (wmod 40)) = .ok target 0 ∧
      Objects.StateRepr 128 1 8 (Frag.init Γ)
        ((before.adopt grown).1.setLocal destination (some grown.val)) base target ∧
      Objects.AllocatorRepr grown.heap base 8 (wmod 49) target ∧
      Objects.Gap grown.heap base 24 40 ∧ target.mem 2 = w[40] ∧ target.mem 1 = w[16] := by
  refine ⟨old_gap,?_⟩
  rcases chosen.nestedDeepFramedBindExecute before bases (wmod 40) (initial (wmod 40)) destination
      (represented _ _ (by decide)) (allocator _ (by decide) _) (by decide) with success | refusal
  · obtain ⟨reference,resolution,fits,base,target,ran,post,allocated,root,extension,stack,localCell,below,gaps,keeps,fresh,newContents,oldContents⟩ := success
    rw [resolved] at resolution
    cases resolution
    have actual : Objects.AllocatorRepr grown.heap base 8 (wmod 49) target := by
      simpa only [before,state,grown,snapshot,demand] using allocated
    exact ⟨base,target,ran,post,actual,gaps 24 40 old_gap (by decide),localCell,
      (below 1 (by decide) (by decide) (by decide)).trans rfl⟩
  · rcases refusal with ⟨refused,_⟩ | ⟨reference,resolution,tooLarge,_⟩
    · rw [resolved] at refused; cases refused
    · rw [resolved] at resolution; cases resolution
      have fits : (wmod 40).val + memoryParentDemand heap .uint old < W := by rw [demand]; decide
      exact (tooLarge fits).elim

theorem gap_overlapping_old_child_refuted : ¬ Objects.Gap heap bases 21 22 := by
  intro gap
  have boundary : (bases oldChild.id).val + Objects.cells heap oldChild ≤ 21 ∨ 22 ≤ (bases oldChild.id).val := gap oldChild
  have neither : ¬ ((bases oldChild.id).val + Objects.cells heap oldChild ≤ 21 ∨ 22 ≤ (bases oldChild.id).val) := by decide +kernel
  exact neither boundary

private def observe (result : Evm.Out) : Option (Evm.Word × Evm.Word × Evm.Word × Evm.Word × Evm.Word × Evm.Word) :=
  match result with
  | .ok target _ => some (target.mem 0,target.mem 1,target.mem 2,target.mem 40,target.mem 41,target.mem 42)
  | _ => none

theorem alias_keeps_identity :
    TRun.rebindMem destination (.alias path) before =
      .ok ⟨before.setLocal destination (some old),List.prefix_refl _⟩ ∧
    observe (run (chosen.code destination) (initial (wmod 40))) =
      some (w[40],w[16],w[16],w[0],w[0],w[0]) := by
  constructor
  · simp only [TRun.rebindMem,MRhs.evalT,resolved,bind,Except.bind,pure,Except.pure]
  · decide +kernel

private def words : List Evm.Word := [w[11],w[23]]
private def copied (machine : Machine) (cursor : Fin W) : Machine :=
  arrayWordsMachine cursor 1 words (allocateMachine machine cursor (wmod 2))
private def stored (machine : Machine) (cursor index : Fin W) : Machine :=
  Objects.defaultStoreMachine (copied machine cursor) (wmod 40) index cursor 1
private def firstMachine : Machine := allocateMachine (initial (wmod 40)) (wmod 40) (wmod 2)
private def secondMachine : Machine := stored firstMachine (wmod 43) (wmod 0)
private def thirdMachine : Machine := stored secondMachine (wmod 46) (wmod 1)

private theorem observed_turn (machine : Machine) (cursor index : Fin W)
    (cell : machine.mem 0 = .val cursor) (header : machine.mem 20 = w[2])
    (room : 23 ≤ cursor.val) (fits : cursor.val + 3 < W)
    (contents : ∀ offset word, words[offset]? = some word → machine.mem (21 + offset) = word)
    (selection : run (nestedMemorySelectCode .uint) (nestedMemoryControl machine (wmod 16) (wmod 40) (wmod 2) index) =
      .ok ((nestedMemoryControl machine (wmod 16) (wmod 40) (wmod 2) index).push w[20]) 0) :
    run (nestedMemoryTurnCode .uint) (nestedMemoryControl machine (wmod 16) (wmod 40) (wmod 2) index) =
      .ok (nestedMemoryControl (stored machine cursor index) (wmod 16) (wmod 40) (wmod 2) (wmod (index.val + 1))) 0 := by
  let controlled := nestedMemoryControl machine (wmod 16) (wmod 40) (wmod 2) index
  have guarded : run memoryArrayCapacityGuard (controlled.push w[20]) = .ok (controlled.push w[20]) 0 := by
    have guard : run memoryArrayCapacityGuard (controlled.push w[20]) =
        if cursor.val + ((wmod 2).val + 1) < W then .ok (controlled.push w[20]) 0 else .revert :=
      memory_capacity_guard_run controlled (wmod 20) cursor (wmod 2) cell header
    rw [show (wmod 2).val = 2 by decide,if_pos fits] at guard
    exact guard
  have copiedRun : run runtimeMemoryArrayCode (controlled.push w[20]) =
      .ok ((copied controlled cursor).push (.val cursor)) 0 :=
    runtime_memory_array_run controlled cursor (wmod 20) words (by decide) cell header (by decide) room contents (by simp only [words,List.length_cons,List.length_nil]; omega)
  have childRun : run checkedMemoryArrayCode (controlled.push w[20]) =
      .ok ((copied controlled cursor).push (.val cursor)) 0 := by
    rw [checkedMemoryArrayCode,run_append_ok guarded]
    exact copiedRun
  have shape : copied controlled cursor = nestedMemoryControl (copied machine cursor) (wmod 16) (wmod 40) (wmod 2) index := by
    rfl
  rw [nestedMemoryTurnCode,run_append_ok selection,run_append_ok childRun,shape]
  exact Objects.defaultStoreStep_run ((copied machine cursor).push w[16]) (wmod 40) (wmod 2) index cursor 1

private theorem observed_selection (machine : Machine) (index : Fin W) (more : index.val < 2)
    (header : machine.mem 16 = w[2]) (pointer : machine.mem (17 + index.val) = w[20]) :
    run (nestedMemorySelectCode .uint) (nestedMemoryControl machine (wmod 16) (wmod 40) (wmod 2) index) =
      .ok ((nestedMemoryControl machine (wmod 16) (wmod 40) (wmod 2) index).push w[20]) 0 := by
  let controlled := nestedMemoryControl machine (wmod 16) (wmod 40) (wmod 2) index
  have addressRun : run arrayAddrStackCode ((controlled.push w[16]).push (.val index)) =
      .ok (controlled.push (.val (wmod ((wmod 16).val + 1 + index.val)))) 0 := by
    have addressed : run arrayAddrStackCode ((controlled.push w[16]).push (.val index)) =
        if index.val < 2 then .ok (controlled.push (.val (wmod ((wmod 16).val + 1 + index.val)))) 0 else .revert :=
      arrayAddrStack_run controlled (wmod 16) index 2 (by decide) header
    rw [if_pos more] at addressed
    exact addressed
  have addressValue : (wmod ((wmod 16).val + 1 + index.val)).val = 17 + index.val := by
    change ((wmod 16).val + 1 + index.val) % W = 17 + index.val
    rw [show (wmod 16).val = 16 by decide]
    exact Nat.mod_eq_of_lt (by
      have large : 20 < W := by decide
      omega)
  rw [nestedMemorySelectCode,run_append_ok (nested_memory_operands machine (wmod 16) (wmod 40) (wmod 2) index)]
  change run (arrayAddrStackCode ++ [.mloadAt]) ((controlled.push w[16]).push (.val index)) = .ok (controlled.push w[20]) 0
  rw [run_append_ok addressRun]
  change Evm.Out.ok (controlled.push (controlled.mem (wmod ((wmod 16).val + 1 + index.val)).val)) 0 = Evm.Out.ok (controlled.push w[20]) 0
  rw [addressValue]
  exact congrArg (fun word => Evm.Out.ok (controlled.push word) 0) pointer

private theorem first_turn :
    run (nestedMemoryTurnCode .uint) (nestedMemoryControl firstMachine (wmod 16) (wmod 40) (wmod 2) (wmod 0)) =
      .ok (nestedMemoryControl secondMachine (wmod 16) (wmod 40) (wmod 2) (wmod 1)) 0 := by
  refine observed_turn firstMachine (wmod 43) (wmod 0) ?_ ?_ (by decide) (by decide) ?_ ?_
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · intro offset word selected
    cases offset with
    | zero => cases selected; with_unfolding_all rfl
    | succ offset => cases offset with
      | zero => cases selected; with_unfolding_all rfl
      | succ offset => cases selected
  · exact observed_selection firstMachine (wmod 0) (by decide) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

private theorem second_turn :
    run (nestedMemoryTurnCode .uint) (nestedMemoryControl secondMachine (wmod 16) (wmod 40) (wmod 2) (wmod 1)) =
      .ok (nestedMemoryControl thirdMachine (wmod 16) (wmod 40) (wmod 2) (wmod 2)) 0 := by
  refine observed_turn secondMachine (wmod 46) (wmod 1) ?_ ?_ (by decide) (by decide) ?_ ?_
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · intro offset word selected
    cases offset with
    | zero => cases selected; with_unfolding_all rfl
    | succ offset => cases offset with
      | zero => cases selected; with_unfolding_all rfl
      | succ offset => cases selected
  · exact observed_selection secondMachine (wmod 1) (by decide) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

private theorem actual_loop :
    run (nestedMemoryLoopCode .uint) (nestedMemoryControl firstMachine (wmod 16) (wmod 40) (wmod 2) (wmod 0)) =
      .ok (nestedMemoryControl thirdMachine (wmod 16) (wmod 40) (wmod 2) (wmod 2)) 0 := by
  apply nested_memory_loop_run
  show loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode .uint)) 3
    (nestedMemoryControl firstMachine (wmod 16) (wmod 40) (wmod 2) (wmod 0)) = _
  simp only [loopIterN,nested_memory_loop_more .uint firstMachine _ (wmod 16) (wmod 40) (wmod 2) (wmod 0) (by decide) first_turn,
    nested_memory_loop_more .uint secondMachine _ (wmod 16) (wmod 40) (wmod 2) (wmod 1) (by decide) second_turn,
    nested_memory_loop_done]

private theorem local_store_run (machine : Machine) (address : Nat) (word : Evm.Word) :
    run [.mstore address] (machine.push word) = .ok (writeMachine machine address word) 0 := by rfl

private theorem actual_deep_run : run (chosen.nestedDeepBindCode destination) (initial (wmod 40)) =
    .ok (writeMachine thirdMachine 2 w[40]) 0 := by
  have pointerRun : run chosen.pointer.code (initial (wmod 40)) = .ok ((initial (wmod 40)).push w[16]) 0 := by
    with_unfolding_all rfl
  have enter : run [.dup 1,.mloadAt] ((initial (wmod 40)).push w[16]) =
      .ok (((initial (wmod 40)).push w[16]).push w[2]) 0 := by with_unfolding_all rfl
  have guard : run (referenceCapacityGuard 0) (((initial (wmod 40)).push w[16]).push w[2]) =
      .ok (((initial (wmod 40)).push w[16]).push w[2]) 0 := by
    simpa only [if_pos (show (wmod 40).val + (wmod 2).val + 1 < W by decide)] using
      nested_memory_parent_guard (initial (wmod 40)) (wmod 16) (wmod 40) (wmod 2) rfl
  have prefixRun : run Objects.nestedPrefix (((initial (wmod 40)).push w[16]).push w[2]) =
      .ok (nestedMemoryControl firstMachine (wmod 16) (wmod 40) (wmod 2) (wmod 0)) 0 :=
    nested_memory_parent_prefix (initial (wmod 40)) (wmod 16) (wmod 40) (wmod 2) rfl
  have exit : run nestedStorageParentExit (nestedMemoryControl thirdMachine (wmod 16) (wmod 40) (wmod 2) (wmod 2)) =
      .ok (thirdMachine.push w[40]) 0 := nested_memory_parent_exit thirdMachine (wmod 16) (wmod 40) (wmod 2)
  simp only [SelectedAlias.nestedDeepBindCode,SelectedAlias.nestedDeepCode,nestedMemoryParentCode,nestedMemoryParentBody,List.append_assoc]
  rw [run_append_ok pointerRun,run_append_ok enter,run_append_ok guard,run_append_ok prefixRun,run_append_ok actual_loop,run_append_ok exit]
  exact local_store_run thirdMachine 2 w[40]

theorem deep_changes_identity :
    observe (run (chosen.nestedDeepBindCode destination) (initial (wmod 40))) =
      some (w[49],w[16],w[40],w[2],w[43],w[46]) := by
  rw [actual_deep_run]
  decide +kernel

private def saturated : Fin W := ⟨W-1,by have positive : 0 < W := W_pos; omega⟩

theorem capacity_refusal :
    path.mvalT before = .ok old ∧
    run (chosen.nestedDeepBindCode destination) (initial saturated) = .revert := by
  refine ⟨resolved,?_⟩
  rcases chosen.nestedDeepBindExecute before bases saturated (initial saturated) destination
      (represented _ _ (by decide)) (allocator _ (by with_unfolding_all decide) _) (by decide) with success | refusal
  · obtain ⟨reference,resolution,fits,_⟩ := success
    rw [resolved] at resolution; cases resolution
    change saturated.val + memoryParentDemand heap .uint old < W at fits
    rw [demand] at fits
    have impossible : ¬ saturated.val + 9 < W := by with_unfolding_all decide
    exact (impossible fits).elim
  · rcases refusal with ⟨refused,_⟩ | ⟨reference,resolution,tooLarge,failed⟩
    · rw [resolved] at refused; cases refused
    · exact failed

theorem wrong_alias_for_deep_copy :
    observe (run (chosen.nestedDeepBindCode destination) (initial (wmod 40))) ≠
      some (w[40],w[16],w[16],w[0],w[0],w[0]) := by rw [deep_changes_identity]; decide

/--
info: 'Solidity.Backend.MemoryCopies.NestedMemoryPathControls.populated_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms populated_inputs
/--
info: 'Solidity.Backend.MemoryCopies.NestedMemoryPathControls.old_child_is_shared' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms old_child_is_shared
/--
info: 'Solidity.Backend.MemoryCopies.NestedMemoryPathControls.copied_children_are_distinct' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms copied_children_are_distinct
/--
info: 'Solidity.Backend.MemoryCopies.NestedMemoryPathControls.actual_deep_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_deep_bind
/--
info: 'Solidity.Backend.MemoryCopies.NestedMemoryPathControls.alias_keeps_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms alias_keeps_identity
/--
info: 'Solidity.Backend.MemoryCopies.NestedMemoryPathControls.deep_changes_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms deep_changes_identity
/--
info: 'Solidity.Backend.MemoryCopies.NestedMemoryPathControls.capacity_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms capacity_refusal
/--
info: 'Solidity.Backend.MemoryCopies.NestedMemoryPathControls.wrong_alias_for_deep_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_alias_for_deep_copy
/--
info: 'Solidity.Backend.MemoryCopies.NestedMemoryPathControls.deep_bind_preserves_inhabited_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms deep_bind_preserves_inhabited_gap
/--
info: 'Solidity.Backend.MemoryCopies.NestedMemoryPathControls.gap_overlapping_old_child_refuted' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms gap_overlapping_old_child_refuted

end Solidity.Backend.MemoryCopies.NestedMemoryPathControls
