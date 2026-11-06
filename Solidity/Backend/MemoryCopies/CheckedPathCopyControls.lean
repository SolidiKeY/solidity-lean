import Solidity.Backend.MemoryCopies.CheckedPathCopy
import Solidity.Backend.MemoryCopies.MemoryPathCopyInterface
import Solidity.Evm.Correct
import Solidity.Evm.MemoryObjectArrayExamples

/-! Existing local and indexed pointer compilation feeds the actual copy loop.
Fresh binding differs from Source alias binding, including empty arrays. -/
namespace Solidity.Backend.MemoryCopies.CheckedPathCopyControls
open Evm Evm.Memory Semantics
private abbrev R : RefTy := .array (.prim .uint)
private abbrev H : HTy := [R]
private def old : HRef H R := ⟨0,rfl⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 256 < W := by decide
private def heap (payloads : List (Fin W)) (bounded : payloads.length < 128) : Heap H :=
  (⟨values payloads,by rw [values,List.length_map]; omega⟩,())
private theorem heap_length (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (heap payloads bounded).len old .dyn = payloads.length := by
  with_unfolding_all change (values payloads).length = payloads.length
  rw [values,List.length_map]
private theorem snapshot (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    MVal.copyMToSt (heap payloads bounded) (T := .ref R) old =
      primitiveArrayValue .uint (values payloads) (by rw [values,List.length_map]; have large : 256 < W := wide; omega) := by
  rw [primitiveArray_snapshot]
  with_unfolding_all rfl
private def bases : Nat → Fin W := fun _ => wmod 16
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with stack := [w[77]],mem := fun address =>
    if address = 0 then w[256] else if address = 1 ∨ address = 2 then w[16]
    else if address = 7 then w[99] else if address = 16 then .val (wmod payloads.length)
    else if 17 ≤ address ∧ address < 17 + payloads.length then .val (payloads[address - 17]?.getD (wmod 0)) else w[0]}
private theorem refs {Q : RefTy} (reference : HRef H Q) : Q = R ∧ HEq reference old := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact ⟨rfl,HEq.rfl⟩
  | succ index => cases selected
private theorem heap_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.HeapRepr (heap payloads bounded) bases 8 (machine payloads) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    decide
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    have large : 256 < W := wide
    with_unfolding_all change 16 + (1 + (values payloads).length) ≤ W
    rw [values,List.length_map]
    omega
  · intro Q S left right different
    obtain ⟨rfl,leftEq⟩ := refs left
    obtain ⟨rfl,rightEq⟩ := refs right
    cases leftEq
    cases rightEq
    exact (different rfl).elim
  · intro A E shape reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    cases shape
    refine ⟨?_,?_,?_⟩
    · have large : 256 < W := wide
      with_unfolding_all change 16 + (1 + (values payloads).length) ≤ W
      rw [values,List.length_map]
      omega
    · intro _
      with_unfolding_all change .val (wmod payloads.length) = Word.val (wmod (values payloads).length)
      rw [values,List.length_map]
    · intro index item selected
      with_unfolding_all change ((values payloads)[index]? = some item) at selected
      simp only [values,List.getElem?_map] at selected
      cases chosen : payloads[index]? with
      | none => simp only [chosen,Option.map_none] at selected; cases selected
      | some payload =>
        simp only [chosen,Option.map_some] at selected
        cases selected
        have lower : index < payloads.length := lt_of_getElem? chosen
        change ReprV .uint (indexValue payload) ((machine payloads).mem (17 + index))
        simp only [machine,if_neg (show 17 + index ≠ 0 by omega),
          if_neg (show ¬(17 + index = 1 ∨ 17 + index = 2) by omega),
          if_neg (show 17 + index ≠ 7 by omega),if_neg (show 17 + index ≠ 16 by omega),
          if_pos (show 17 ≤ 17 + index ∧ 17 + index < 17 + payloads.length by omega),
          Nat.add_sub_cancel_left,chosen,Option.getD_some]
        exact ReprV.uint_of rfl
  · intro name reference
    obtain ⟨different,_⟩ := refs reference
    cases different
  · intro name field Q reference fieldType
    obtain ⟨different,_⟩ := refs reference
    cases different
private theorem allocator (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.AllocatorRepr (heap payloads bounded) bases 8 (wmod 256) (machine payloads) := by
  refine ⟨heap_repr payloads bounded,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro address above
    change 256 ≤ address at above
    simp only [machine,if_neg (show address ≠ 0 by omega),
      if_neg (show ¬(address = 1 ∨ address = 2) by omega),if_neg (show address ≠ 7 by omega),
      if_neg (show address ≠ 16 by omega),
      if_neg (show ¬(17 ≤ address ∧ address < 17 + payloads.length) by omega)]
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    with_unfolding_all change 16 + (1 + (values payloads).length) ≤ 256
    rw [values,List.length_map]
    omega
private def C : Contract := {vars := []}
private abbrev Γ : Ctx := [.mem R,.mem R]
private def state (payloads : List (Fin W)) (bounded : payloads.length < 128) : State C Γ :=
  {storage := Storage.init C,H := H,heap := heap payloads bounded,env := (some old,(some old,()))}
private def path : MPath C Γ (.ref R) := .var .here rfl
private def destination : Idx Γ (.mem R) := .there .here
private def chosen : SelectedAlias 1 (Frag.init Γ) path := selectedAlias 1 (Frag.init Γ) path rfl
private theorem core (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Sim C 128 1 (Frag.init Γ) (state payloads bounded) (machine payloads) := by
  have initial : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) (Machine.init (fun _ => 0) ⟨0,W_pos⟩) :=
    Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,?_,?_,initial.net,initial.netSelf,by unfold Lmax; decide,?_,initial.env,initial.funds,initial.oracle⟩
  · intro name type found
    with_unfolding_all cases found
  all_goals intro p index
  all_goals cases index with
    | there index => cases index with
      | there index => nomatch index
private theorem represented (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.StateRepr 128 1 8 (Frag.init Γ) (state payloads bounded) bases (machine payloads) := by
  refine ⟨core payloads bounded,heap_repr payloads bounded,?_,by decide⟩
  intro Q index
  cases index with
  | here => exact ⟨old,rfl,rfl⟩
  | there index => cases index with
    | here => exact ⟨old,rfl,rfl⟩
    | there index => nomatch index
private theorem resolved (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    path.mvalT (state payloads bounded) = .ok old := by with_unfolding_all rfl
private theorem room (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (fits : 256 + (payloads.length + 1) < W) : MemoryPathRoom (state payloads bounded) (wmod 256) path := by
  intro reference evaluated
  rw [resolved payloads bounded] at evaluated
  cases evaluated
  change 256 + ((heap payloads bounded).len old .dyn + 1) < W
  rw [heap_length]
  exact fits
private def grown (payloads : List (Fin W)) (bounded : payloads.length < 128) :=
  (MVal.copyMToSt (heap payloads bounded) (T := .ref R) old).copyStToM (heap payloads bounded) rfl
private def after (payloads : List (Fin W)) (bounded : payloads.length < 128) :=
  ((state payloads bounded).adopt (grown payloads bounded)).1.setLocal destination (some (grown payloads bounded).val)

theorem certificate_inhabited : CheckedPathCopyCertificate := checkedPathCopy

private theorem failure_impossible {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (cursor : Fin W) (path : MPath C Γ (.ref (.array (.prim primitive))))
    (reference : HRef state.H (.array (.prim primitive))) (resolved : path.mvalT state = .ok reference)
    (fits : cursor.val + (state.heap.len reference .dyn + 1) < W) : ¬ CheckedPathFailure state cursor path := by
  intro failed
  rcases failed with refused | ⟨other,evaluated,nofit⟩
  · rw [resolved] at refused
    cases refused
  · rw [resolved] at evaluated
    cases evaluated
    exact nofit fits

theorem actual_binding (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (fits : 256 + (payloads.length + 1) < W) :
    ∃ (base' : Nat → Fin W) (target : Machine),
      run (chosen.checkedDeepBindCode destination) (machine payloads) = .ok target 0 ∧
      Objects.AllocatorRepr (grown payloads bounded).heap base' 8 ⟨256 + (payloads.length + 1),fits⟩ target ∧
      target.mem 0 = .val (wmod (256 + payloads.length + 1)) ∧
      target.mem 256 = .val (wmod payloads.length) ∧ target.mem 1 = w[256] ∧ target.mem 2 = w[16] ∧
      target.mem 7 = w[99] ∧ target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload →
        target.mem (257 + index) = .val payload ∧ target.mem (17 + index) = .val payload) := by
  rcases chosen.checkedDeepBindExecute (represented payloads bounded) (allocator payloads bounded) (by decide)
      destination with
    ⟨reference,evaluated,actualFits,base',target,ran,_,allocated,root,_,stack,localAt,below,_,_⟩ | ⟨refused,_⟩
  · rw [resolved payloads bounded] at evaluated
    cases evaluated
    have reached : Objects.AllocatorRepr (grown payloads bounded).heap base' 8 ⟨256 + (payloads.length + 1),fits⟩ target := by
      simpa only [state,heap_length] using allocated
    change base' (grown payloads bounded).val.id = wmod 256 at root
    have sourceLength : (grown payloads bounded).heap.len (grown payloads bounded).val .dyn = payloads.length := by
      dsimp only [grown]
      rw [snapshot,primitive_array_source]
      simp only [Grown.alloc,Heap.len,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,
        heap,values,List.length_map]
    have header : target.mem (base' (grown payloads bounded).val.id).val = .val (wmod payloads.length) := by
      have stored : target.mem (base' (grown payloads bounded).val.id).val =
          .val (wmod ((grown payloads bounded).heap.len (grown payloads bounded).val .dyn)) :=
        (allocated.heap.arrays .dyn (grown payloads bounded).val).length rfl
      rw [sourceLength] at stored
      exact stored
    rw [root] at header
    refine ⟨base',target,ran,reached,?_,header,localAt,below 2 (by decide) (by decide) (by decide),
      below 7 (by decide) (by decide) (by decide),stack,?_⟩
    · refine reached.free.cell.trans ?_
      apply congrArg Word.val
      apply Fin.ext
      change 256 + (payloads.length + 1) = (256 + payloads.length + 1) % W
      exact (Nat.mod_eq_of_lt (by omega)).symm
    · intro index payload selected
      have lower : index < payloads.length := lt_of_getElem? selected
      have item : (MObj.elems .dyn ((grown payloads bounded).heap.get (grown payloads bounded).val))[index]? = some (indexValue payload) := by
        dsimp only [grown]
        rw [snapshot,primitive_array_source]
        simp only [Grown.alloc,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,MVal.wk,
          heap,values,List.getElem?_map,selected,Option.map_some]
      have contents : ReprV .uint (indexValue payload) (target.mem ((base' (grown payloads bounded).val.id).val + 1 + index)) :=
        (allocated.heap.arrays .dyn (grown payloads bounded).val).elements index (indexValue payload) item
      obtain ⟨word,stored,equal⟩ := contents
      have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
      subst word
      rw [root] at stored
      refine ⟨stored,?_⟩
      rw [below (17 + index) (by omega) (by change 17 + index < 256; omega) (by change 17 + index ≠ 1; omega)]
      simp only [machine,if_neg (show 17 + index ≠ 0 by omega),
        if_neg (show ¬(17 + index = 1 ∨ 17 + index = 2) by omega),
        if_neg (show 17 + index ≠ 7 by omega),if_neg (show 17 + index ≠ 16 by omega),
        if_pos (show 17 ≤ 17 + index ∧ 17 + index < 17 + payloads.length by omega),
        Nat.add_sub_cancel_left,selected,Option.getD_some]
  
  · exact (failure_impossible (state payloads bounded) (wmod 256) path old (resolved payloads bounded) ((room payloads bounded fits) old (resolved payloads bounded)) refused).elim

theorem pair_binding (left right : Fin W) : ∃ target : Machine,
    run (chosen.checkedDeepBindCode destination) (machine [left,right]) = .ok target 0 ∧
      target.mem 0 = w[259] ∧ target.mem 1 = w[256] ∧ target.mem 2 = w[16] ∧
      target.mem 257 = .val left ∧ target.mem 258 = .val right ∧ target.mem 17 = .val left ∧ target.mem 18 = .val right := by
  obtain ⟨_,target,ran,_,cursor,_,fresh,alias,_,_,contents⟩ :=
    actual_binding [left,right] (by change 2 < 128; decide) (by change 256 + (2 + 1) < W; decide)
  exact ⟨target,ran,cursor,fresh,alias,(contents 0 left rfl).1,(contents 1 right rfl).1,
    (contents 0 left rfl).2,(contents 1 right rfl).2⟩

theorem empty_binding : ∃ target : Machine,
    run (chosen.checkedDeepBindCode destination) (machine []) = .ok target 0 ∧
      target.mem 0 = w[257] ∧ target.mem 1 = w[256] ∧ target.mem 2 = w[16] ∧ target.mem 256 = w[0] := by
  obtain ⟨_,target,ran,_,cursor,header,fresh,alias,_,_,_⟩ := actual_binding [] (by decide) (by decide)
  exact ⟨target,ran,cursor,fresh,alias,header⟩
private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))
theorem long_binding : ∃ target : Machine,
    run (chosen.checkedDeepBindCode destination) (machine long) = .ok target 0 ∧
      target.mem 0 = w[321] ∧ target.mem 1 = w[256] ∧ target.mem 2 = w[16] ∧ target.mem 320 = w[64] ∧ target.mem 80 = w[64] := by
  obtain ⟨_,target,ran,_,cursor,_,fresh,alias,_,_,contents⟩ :=
    actual_binding long (by rw [long,List.length_ofFn]; decide) (by rw [long,List.length_ofFn]; decide)
  exact ⟨target,ran,cursor,fresh,alias,(contents 63 (wmod 64) (by decide +kernel)).1,
    (contents 63 (wmod 64) (by decide +kernel)).2⟩

theorem alias_source (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    TRun.rebindMem destination (.alias path) (state payloads bounded) =
      .ok ⟨(state payloads bounded).setLocal destination (some old),List.prefix_refl _⟩ := by
  simp only [TRun.rebindMem,MRhs.evalT,resolved,bind,Except.bind,pure,Except.pure]

theorem alias_target (payloads : List (Fin W)) :
    run (chosen.code destination) (machine payloads) = .ok (machine payloads) 0 := by
  have unchanged : upd (machine payloads).mem 1 w[16] = (machine payloads).mem := by
    funext address
    by_cases same : address = 1
    · subst address
      rw [upd_same]
      rfl
    · exact upd_other _ _ same
  with_unfolding_all change Out.ok {machine payloads with mem := upd (machine payloads).mem 1 w[16]} 0 = _
  rw [unchanged]

theorem intrinsic_other_alias (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    TEnv.get (.here : Idx Γ (.mem R)) (after payloads bounded).env = some (old.wk (grown payloads bounded).ext) := by
  with_unfolding_all rfl

theorem old_pointer_rejected (target : Machine)
    (ran : run (chosen.checkedDeepBindCode destination) (machine []) = .ok target 0) : target.mem 1 ≠ w[16] := by
  obtain ⟨actual,execution,_,fresh,_,_⟩ := empty_binding
  rw [ran] at execution
  have same : target.mem 1 = actual.mem 1 := congrArg (fun state => state.mem 1) (Out.ok.inj execution).1
  rw [same,fresh]
  decide

theorem wrong_payload_rejected (target : Machine)
    (ran : run (chosen.checkedDeepBindCode destination) (machine [wmod 11,wmod 23]) = .ok target 0) : target.mem 258 ≠ w[0] := by
  obtain ⟨actual,execution,_,_,_,_,second,_,_⟩ := pair_binding (wmod 11) (wmod 23)
  rw [ran] at execution
  have same : target.mem 258 = actual.mem 258 := congrArg (fun state => state.mem 258) (Out.ok.inj execution).1
  rw [same,second]
  decide

private structure IndexedInput where
  contract : Contract
  context : Ctx
  frag : Frag context
  state : State contract context
  base : Nat → Fin W
  machine : Machine
  represented : Objects.StateRepr 1 1 8 frag state base machine
  allocator : Objects.AllocatorRepr state.heap base 8 (wmod 40) machine
  parent : Idx context (.mem (.fixed (.ref R) 2))
  destination : Idx context (.mem R)
private def indexed : IndexedInput :=
  ⟨_,_,_,_,_,_,ObjectArrayExamples.initial_repr,ObjectArrayExamples.initial_allocator,.here,.there (.there .here)⟩
private def indexedPath (index : Int) (bound : PrimTy.uint.inRange index = true) :
    MPath indexed.contract indexed.context (.ref R) :=
  .loc (.index .fixed (.var indexed.parent rfl) (.simple (.lit index bound)))
private def indexedChosen (index : Int) (bound : PrimTy.uint.inRange index = true) :
    SelectedAlias 1 indexed.frag (indexedPath index bound) := selectedAlias 1 indexed.frag (indexedPath index bound) rfl
private def indexedReference : HRef indexed.state.H R := ⟨0,rfl⟩
private theorem indexed_good : (indexedPath 0 rfl).mvalT indexed.state = .ok indexedReference := by with_unfolding_all rfl
private theorem indexed_room : MemoryPathRoom indexed.state (wmod 40) (indexedPath 0 rfl) := by
  intro reference evaluated
  rw [indexed_good] at evaluated
  cases evaluated
  with_unfolding_all change 40 + (1 + 1) < W
  decide

private theorem indexed_snapshot : MVal.copyMToSt indexed.state.heap (T := .ref R) indexedReference =
    primitiveArrayValue .uint [indexValue (wmod 7)] (by decide) := by
  rw [primitiveArray_snapshot]
  with_unfolding_all rfl

theorem indexed_binding : ∃ target : Machine,
    run ((indexedChosen 0 rfl).checkedDeepBindCode indexed.destination) indexed.machine = .ok target 0 ∧
      target.mem 0 = w[42] ∧ target.mem 1 = w[40] ∧ target.mem 2 = w[24] ∧ target.mem 17 = w[7] ∧ target.mem 41 = w[7] ∧ target.stack = [w[77]] := by
  rcases (indexedChosen 0 rfl).checkedDeepBindExecute indexed.represented indexed.allocator (by decide)
      indexed.destination with
    ⟨reference,evaluated,actualFits,base',target,ran,_,allocated,root,_,stack,localAt,below,_,_⟩ | ⟨refused,_⟩
  · rw [indexed_good] at evaluated
    cases evaluated
    have cursor : target.mem 0 = w[42] := by
      have cell : target.mem 0 = Word.val ⟨(wmod 40).val + (indexed.state.heap.len indexedReference .dyn + 1),
          indexed_room indexedReference indexed_good⟩ := allocated.free.cell
      with_unfolding_all change target.mem 0 = w[42] at cell
      exact cell
    with_unfolding_all change target.mem 1 = w[40] at localAt
    have alias : target.mem 2 = w[24] := by
      have oldAlias : target.mem 2 = indexed.machine.mem 2 := below 2 (by decide) (by decide) (by decide +kernel)
      with_unfolding_all change target.mem 2 = w[24] at oldAlias
      exact oldAlias
    have old : target.mem 17 = w[7] := by
      have oldPayload : target.mem 17 = indexed.machine.mem 17 := below 17 (by decide) (by decide) (by decide +kernel)
      with_unfolding_all change target.mem 17 = w[7] at oldPayload
      exact oldPayload
    let copy := (MVal.copyMToSt indexed.state.heap (T := .ref R) indexedReference).copyStToM indexed.state.heap rfl
    have item : (MObj.elems .dyn (copy.heap.get copy.val))[0]? = some (indexValue (wmod 7)) := by
      dsimp only [copy]
      rw [indexed_snapshot,primitive_array_source]
      with_unfolding_all rfl
    have contents : ReprV .uint (indexValue (wmod 7)) (target.mem ((base' copy.val.id).val + 1 + 0)) :=
      (allocated.heap.arrays .dyn copy.val).elements 0 (indexValue (wmod 7)) item
    obtain ⟨word,stored,equal⟩ := contents
    have same : word = wmod 7 := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    rw [root] at stored
    have payload : target.mem 41 = w[7] := stored
    with_unfolding_all change target.stack = [w[77]] at stack
    exact ⟨target,ran,cursor,localAt,alias,old,payload,stack⟩
  · exact (failure_impossible indexed.state (wmod 40) (indexedPath 0 rfl) indexedReference indexed_good (indexed_room indexedReference indexed_good) refused).elim

private theorem indexed_bad : (indexedPath 2 rfl).mvalT indexed.state = .error .revert := by with_unfolding_all rfl
private theorem indexed_bad_room : MemoryPathRoom indexed.state (wmod 40) (indexedPath 2 rfl) := by
  intro reference evaluated
  rw [indexed_bad] at evaluated
  cases evaluated

theorem indexed_refusal :
    (indexedPath 2 rfl).mvalT indexed.state = .error .revert ∧
    run ((indexedChosen 2 rfl).checkedDeepBindCode indexed.destination) indexed.machine = .revert := by
  rcases (indexedChosen 2 rfl).checkedDeepBindExecute indexed.represented indexed.allocator (by decide)
      indexed.destination with ⟨reference,evaluated,_⟩ | failed
  · rw [indexed_bad] at evaluated
    cases evaluated
  · exact ⟨indexed_bad,failed.2⟩

private def saturated (payloads : List (Fin W)) : Machine := writeMachine (machine payloads) 0 (.val wMax)
private theorem saturated_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.StateRepr 128 1 8 (Frag.init Γ) (state payloads bounded) bases (saturated payloads) := by
  have initial : Objects.StateRepr 128 1 8 (Frag.init Γ) (state payloads bounded) bases (machine payloads) := represented payloads bounded
  refine ⟨initial.core.congrMem ?_,initial.heap.localWrite 0 (by decide) (.val wMax),?_,initial.locals⟩
  · intro level lower upper
    exact upd_other _ _ (by change level ≠ 0; omega)
  · intro Q index
    obtain ⟨reference,found,word⟩ := initial.pointers index
    refine ⟨reference,found,?_⟩
    change upd (machine payloads).mem 0 (.val wMax) (cellOf 1 index) = _
    rw [upd_other _ _ (by have lower : 1 ≤ lvl 1 index := le_lvl 1 index; change lvl 1 index ≠ 0; omega)]
    exact word
private theorem saturated_allocator (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.AllocatorRepr (state payloads bounded).heap bases 8 wMax (saturated payloads) := by
  have initial : Objects.AllocatorRepr (heap payloads bounded) bases 8 (wmod 256) (machine payloads) := allocator payloads bounded
  have high : 256 ≤ wMax.val := by decide
  refine ⟨initial.heap.localWrite 0 (by decide) (.val wMax),⟨by decide,by omega,?_,?_⟩,?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (initial.free.zero address (by change 256 ≤ address; omega))
  · intro Q reference
    have live : (bases reference.id).val + Objects.cells (heap payloads bounded) reference ≤ 256 := initial.live reference
    exact Nat.le_trans live high

theorem capacity_refusal (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    path.mvalT (state payloads bounded) = .ok old ∧
    ¬ wMax.val + ((state payloads bounded).heap.len old .dyn + 1) < W ∧
    run (chosen.checkedDeepBindCode destination) (saturated payloads) = .revert := by
  have nofit : ¬ wMax.val + ((state payloads bounded).heap.len old .dyn + 1) < W := by
    change ¬ (W - 1 + (_ + 1) < W)
    have positive : 0 < W := W_pos
    omega
  refine ⟨resolved payloads bounded,nofit,?_⟩
  rcases chosen.checkedDeepBindExecute (saturated_repr payloads bounded) (saturated_allocator payloads bounded) (by decide) destination with
    ⟨reference,evaluated,fits,_⟩ | failed
  · rw [resolved payloads bounded] at evaluated
    cases evaluated
    exact (nofit fits).elim
  · exact failed.2

theorem empty_capacity_refusal :
    run (chosen.checkedDeepBindCode destination) (saturated []) = .revert :=
  (capacity_refusal [] (by decide)).2.2

#print axioms certificate_inhabited
#print axioms actual_binding
#print axioms pair_binding
#print axioms empty_binding
#print axioms long_binding
#print axioms alias_source
#print axioms alias_target
#print axioms intrinsic_other_alias
#print axioms old_pointer_rejected
#print axioms wrong_payload_rejected
#print axioms indexed_binding
#print axioms indexed_refusal
#print axioms capacity_refusal
#print axioms empty_capacity_refusal
end Solidity.Backend.MemoryCopies.CheckedPathCopyControls
