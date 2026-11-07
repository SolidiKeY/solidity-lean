import Solidity.Backend.MemoryCopies.CheckedFixedPathCopy
import Solidity.Evm.Correct
import Solidity.Evm.MemoryFixedChildArrayExamples

/-! Existing selected pointers feed headerless fixed copies and fresh binding.
Actual alias semantics and invalid indexed paths remain separate observations. -/
namespace Solidity.Backend.MemoryCopies.CheckedFixedPathCopyControls
open Evm Evm.Memory Semantics
private def R (count : Nat) : RefTy := .fixed (.prim .uint) count
private def H (count : Nat) : HTy := [R count]
private def old (count : Nat) : HRef (H count) (R count) := ⟨0,rfl⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 256 < W := by decide
private def heap (payloads : List (Fin W)) : Heap (H payloads.length) :=
  (⟨values payloads,by rw [values,List.length_map]⟩,())
private def bases : Nat → Fin W := fun _ => wmod 16
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with stack := [w[77]],mem := fun address =>
    if address = 0 then w[256] else if address = 1 ∨ address = 2 then w[16]
    else if address = 7 then w[99]
    else if 16 ≤ address ∧ address < 16 + payloads.length then .val (payloads[address - 16]?.getD (wmod 0)) else w[0]}
private theorem refs {count : Nat} {Q : RefTy} (reference : HRef (H count) Q) : Q = R count ∧ HEq reference (old count) := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact ⟨rfl,HEq.rfl⟩
  | succ index => cases selected
private theorem snapshot (payloads : List (Fin W)) :
    MVal.copyMToSt (heap payloads) (T := .ref (R payloads.length)) (old payloads.length) =
      fixedPrimitiveValue .uint payloads.length (values payloads) (by rw [values,List.length_map]) := by
  rw [primitiveFixed_snapshot]
  with_unfolding_all rfl
private theorem heap_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.HeapRepr (heap payloads) bases 8 (machine payloads) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    change 8 ≤ 16
    decide
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    have large : 256 < W := wide
    with_unfolding_all change 16 + max 1 payloads.length ≤ W
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
      with_unfolding_all change 16 + max 1 payloads.length ≤ W
      omega
    · intro impossible
      cases impossible
    · intro index item selected
      with_unfolding_all change (values payloads)[index]? = some item at selected
      simp only [values,List.getElem?_map] at selected
      cases chosen : payloads[index]? with
      | none => simp only [chosen,Option.map_none] at selected; cases selected
      | some payload =>
        simp only [chosen,Option.map_some] at selected
        cases selected
        have lower : index < payloads.length := lt_of_getElem? chosen
        change ReprV .uint (indexValue payload) ((machine payloads).mem (16 + index))
        simp only [machine,if_neg (show 16 + index ≠ 0 by omega),
          if_neg (show ¬(16 + index = 1 ∨ 16 + index = 2) by omega),if_neg (show 16 + index ≠ 7 by omega),
          if_pos (show 16 ≤ 16 + index ∧ 16 + index < 16 + payloads.length by omega),
          Nat.add_sub_cancel_left,chosen,Option.getD_some]
        exact ReprV.uint_of rfl
  · intro name reference
    obtain ⟨different,_⟩ := refs reference
    cases different
  · intro name field Q reference fieldType
    obtain ⟨different,_⟩ := refs reference
    cases different
private theorem allocator (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.AllocatorRepr (heap payloads) bases 8 (wmod 256) (machine payloads) := by
  refine ⟨heap_repr payloads bounded,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro address above
    change 256 ≤ address at above
    simp only [machine,if_neg (show address ≠ 0 by omega),
      if_neg (show ¬(address = 1 ∨ address = 2) by omega),if_neg (show address ≠ 7 by omega),
      if_neg (show ¬(16 ≤ address ∧ address < 16 + payloads.length) by omega)]
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    with_unfolding_all change 16 + max 1 payloads.length ≤ 256
    omega
private def C : Contract := {vars := []}
private def Γ (count : Nat) : Ctx := [.mem (R count),.mem (R count)]
private def state (payloads : List (Fin W)) : State C (Γ payloads.length) :=
  {storage := Storage.init C,H := H payloads.length,heap := heap payloads,env := (some (old payloads.length),(some (old payloads.length),()))}
private def path (count : Nat) : MPath C (Γ count) (.ref (R count)) := .var .here rfl
private def destination (count : Nat) : Idx (Γ count) (.mem (R count)) := .there .here
private def chosen (count : Nat) : SelectedAlias 1 (Frag.init (Γ count)) (path count) :=
  selectedAlias 1 (Frag.init (Γ count)) (path count) rfl
private theorem core (payloads : List (Fin W)) :
    Sim C 128 1 (Frag.init (Γ payloads.length)) (state payloads) (machine payloads) := by
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
    Objects.StateRepr 128 1 8 (Frag.init (Γ payloads.length)) (state payloads) bases (machine payloads) := by
  refine ⟨core payloads,heap_repr payloads bounded,?_,by change 1 + 2 ≤ 8; decide⟩
  intro Q index
  cases index with
  | here => exact ⟨old payloads.length,rfl,rfl⟩
  | there index => cases index with
    | here => exact ⟨old payloads.length,rfl,rfl⟩
    | there index => nomatch index
private theorem resolved (payloads : List (Fin W)) :
    (path payloads.length).mvalT (state payloads) = .ok (old payloads.length) := by with_unfolding_all rfl
private def grown (payloads : List (Fin W)) :=
  (MVal.copyMToSt (heap payloads) (T := .ref (R payloads.length)) (old payloads.length)).copyStToM (heap payloads) rfl
private def after (payloads : List (Fin W)) :=
  ((state payloads).adopt (grown payloads)).1.setLocal (destination payloads.length) (some (grown payloads).val)

theorem certificate_inhabited : CheckedFixedPathCopyCertificate := checkedFixedPathCopy

theorem actual_binding (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (fits : 256 + max 1 payloads.length < W) :
    ∃ (base' : Nat → Fin W) (target : Machine),
      run ((chosen payloads.length).checkedFixedDeepBindCode (destination payloads.length)) (machine payloads) = .ok target 0 ∧
      Objects.AllocatorRepr (grown payloads).heap base' 8 ⟨256 + max 1 payloads.length,fits⟩ target ∧
      target.mem 0 = .val (wmod (256 + max 1 payloads.length)) ∧ target.mem 1 = w[256] ∧ target.mem 2 = w[16] ∧
      target.mem 7 = w[99] ∧ target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload →
        target.mem (256 + index) = .val payload ∧ target.mem (16 + index) = .val payload) := by
  rcases (chosen payloads.length).checkedFixedDeepBindExecute (represented payloads bounded) (allocator payloads bounded)
      (by decide) (destination payloads.length) with
    ⟨reference,evaluated,actualFits,base',target,ran,_,allocated,root,_,stack,localAt,below,_,_⟩ | ⟨refused,_⟩
  · rw [resolved payloads] at evaluated
    cases evaluated
    change base' (grown payloads).val.id = wmod 256 at root
    change target.mem 1 = w[256] at localAt
    refine ⟨base',target,ran,allocated,?_,localAt,below 2 (by decide) (by decide) (by change 2 ≠ 1; decide),
      below 7 (by decide) (by decide) (by change 7 ≠ 1; decide),stack,?_⟩
    · refine allocated.free.cell.trans ?_
      apply congrArg Word.val
      apply Fin.ext
      change 256 + max 1 payloads.length = (256 + max 1 payloads.length) % W
      exact (Nat.mod_eq_of_lt fits).symm
    · intro index payload selected
      have lower : index < payloads.length := lt_of_getElem? selected
      have item : (MObj.elems .fixed ((grown payloads).heap.get (grown payloads).val))[index]? = some (indexValue payload) := by
        dsimp only [grown]
        rw [snapshot,fixed_primitive_source]
        simp only [Grown.alloc,Heap.get_alloc,MObj.elems_fixed,MObj.wk,fixedPrimitiveObject,MVal.wk,
          values,List.getElem?_map,selected,Option.map_some]
      have contents : ReprV .uint (indexValue payload) (target.mem ((base' (grown payloads).val.id).val + 0 + index)) :=
        (allocated.heap.arrays .fixed (grown payloads).val).elements index (indexValue payload) item
      obtain ⟨word,stored,equal⟩ := contents
      have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
      subst word
      rw [root] at stored
      refine ⟨stored,?_⟩
      rw [below (16 + index) (by omega) (by change 16 + index < 256; omega) (by change 16 + index ≠ 1; omega)]
      simp only [machine,if_neg (show 16 + index ≠ 0 by omega),
        if_neg (show ¬(16 + index = 1 ∨ 16 + index = 2) by omega),if_neg (show 16 + index ≠ 7 by omega),
        if_pos (show 16 ≤ 16 + index ∧ 16 + index < 16 + payloads.length by omega),
        Nat.add_sub_cancel_left,selected,Option.getD_some]
  
  · rcases refused with badPath | ⟨_,_,noRoom⟩
    · rw [resolved payloads] at badPath
      cases badPath
    · exact (noRoom fits).elim

theorem pair_binding (left right : Fin W) : ∃ target : Machine,
    run ((chosen 2).checkedFixedDeepBindCode (destination 2)) (machine [left,right]) = .ok target 0 ∧
      target.mem 0 = w[258] ∧ target.mem 1 = w[256] ∧ target.mem 2 = w[16] ∧
      target.mem 256 = .val left ∧ target.mem 257 = .val right ∧ target.mem 16 = .val left ∧ target.mem 17 = .val right := by
  obtain ⟨_,target,ran,_,cursor,fresh,alias,_,_,contents⟩ :=
    actual_binding [left,right] (by change 2 < 128; decide) (by change 256 + max 1 2 < W; decide)
  exact ⟨target,ran,cursor,fresh,alias,(contents 0 left rfl).1,(contents 1 right rfl).1,
    (contents 0 left rfl).2,(contents 1 right rfl).2⟩

theorem empty_binding : ∃ target : Machine,
    run ((chosen 0).checkedFixedDeepBindCode (destination 0)) (machine []) = .ok target 0 ∧
      target.mem 0 = w[257] ∧ target.mem 1 = w[256] ∧ target.mem 2 = w[16] := by
  obtain ⟨_,target,ran,_,cursor,fresh,alias,_,_,_⟩ := actual_binding [] (by decide) (by decide)
  exact ⟨target,ran,cursor,fresh,alias⟩
private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))
theorem long_binding : ∃ target : Machine,
    run ((chosen 64).checkedFixedDeepBindCode (destination 64)) (machine long) = .ok target 0 ∧
      target.mem 0 = w[320] ∧ target.mem 1 = w[256] ∧ target.mem 2 = w[16] ∧ target.mem 319 = w[64] ∧ target.mem 79 = w[64] := by
  obtain ⟨_,target,ran,_,cursor,fresh,alias,_,_,contents⟩ :=
    actual_binding long (by rw [long,List.length_ofFn]; decide) (by rw [long,List.length_ofFn]; decide)
  exact ⟨target,ran,cursor,fresh,alias,(contents 63 (wmod 64) (by decide +kernel)).1,
    (contents 63 (wmod 64) (by decide +kernel)).2⟩

theorem alias_source (payloads : List (Fin W)) :
    TRun.rebindMem (destination payloads.length) (.alias (path payloads.length)) (state payloads) =
      .ok ⟨(state payloads).setLocal (destination payloads.length) (some (old payloads.length)),List.prefix_refl _⟩ := by
  simp only [TRun.rebindMem,MRhs.evalT,resolved,bind,Except.bind,pure,Except.pure]

theorem alias_target (payloads : List (Fin W)) :
    run ((chosen payloads.length).code (destination payloads.length)) (machine payloads) = .ok (machine payloads) 0 := by
  have unchanged : upd (machine payloads).mem 1 w[16] = (machine payloads).mem := by
    funext address
    by_cases same : address = 1
    · subst address
      rw [upd_same]
      rfl
    · exact upd_other _ _ same
  with_unfolding_all change Out.ok {machine payloads with mem := upd (machine payloads).mem 1 w[16]} 0 = _
  rw [unchanged]

theorem intrinsic_other_alias (payloads : List (Fin W)) :
    TEnv.get (.here : Idx (Γ payloads.length) (.mem (R payloads.length))) (after payloads).env =
      some ((old payloads.length).wk (grown payloads).ext) := by with_unfolding_all rfl

theorem old_pointer_rejected (target : Machine)
    (ran : run ((chosen 0).checkedFixedDeepBindCode (destination 0)) (machine []) = .ok target 0) : target.mem 1 ≠ w[16] := by
  obtain ⟨actual,execution,_,fresh,_⟩ := empty_binding
  rw [ran] at execution
  have same : target.mem 1 = actual.mem 1 := congrArg (fun state => state.mem 1) (Out.ok.inj execution).1
  rw [same,fresh]
  decide

theorem header_rejected (target : Machine)
    (ran : run ((chosen 2).checkedFixedDeepBindCode (destination 2)) (machine [wmod 11,wmod 23]) = .ok target 0) : target.mem 256 ≠ w[2] := by
  obtain ⟨actual,execution,_,_,_,first,_,_,_⟩ := pair_binding (wmod 11) (wmod 23)
  rw [ran] at execution
  have same : target.mem 256 = actual.mem 256 := congrArg (fun state => state.mem 256) (Out.ok.inj execution).1
  rw [same,first]
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
  parent : Idx context (.mem (.fixed (.ref (R 1)) 2))
  destination : Idx context (.mem (R 1))
private def indexed : IndexedInput :=
  ⟨_,_,_,_,_,_,FixedChildArrayExamples.initial_repr,FixedChildArrayExamples.initial_allocator,.here,.there (.there .here)⟩
private def indexedPath (index : Int) (bound : PrimTy.uint.inRange index = true) :
    MPath indexed.contract indexed.context (.ref (R 1)) :=
  .loc (.index .fixed (.var indexed.parent rfl) (.simple (.lit index bound)))
private def indexedChosen (index : Int) (bound : PrimTy.uint.inRange index = true) :
    SelectedAlias 1 indexed.frag (indexedPath index bound) := selectedAlias 1 indexed.frag (indexedPath index bound) rfl
private def indexedReference : HRef indexed.state.H (R 1) := ⟨0,rfl⟩
private theorem indexed_good : (indexedPath 0 rfl).mvalT indexed.state = .ok indexedReference := by with_unfolding_all rfl
private theorem indexed_fits : (wmod 40).val + max 1 1 < W := by decide

private theorem indexed_snapshot : MVal.copyMToSt indexed.state.heap (T := .ref (R 1)) indexedReference =
    fixedPrimitiveValue .uint 1 [indexValue (wmod 7)] rfl := by
  rw [primitiveFixed_snapshot]
  with_unfolding_all rfl

theorem indexed_binding : ∃ target : Machine,
    run ((indexedChosen 0 rfl).checkedFixedDeepBindCode indexed.destination) indexed.machine = .ok target 0 ∧
      target.mem 0 = w[41] ∧ target.mem 1 = w[40] ∧ target.mem 2 = w[24] ∧ target.mem 16 = w[7] ∧ target.mem 40 = w[7] ∧ target.stack = [w[77]] := by
  rcases (indexedChosen 0 rfl).checkedFixedDeepBindExecute indexed.represented indexed.allocator (by decide)
      indexed.destination with
    ⟨reference,evaluated,actualFits,base',target,ran,_,allocated,root,_,stack,localAt,below,_,_⟩ | ⟨refused,_⟩
  · rw [indexed_good] at evaluated
    cases evaluated
    have cursor : target.mem 0 = w[41] := by
      have cell : target.mem 0 = Word.val ⟨(wmod 40).val + max 1 1,
          actualFits⟩ := allocated.free.cell
      with_unfolding_all change target.mem 0 = w[41] at cell
      exact cell
    with_unfolding_all change target.mem 1 = w[40] at localAt
    have alias : target.mem 2 = w[24] := by
      have oldAlias : target.mem 2 = indexed.machine.mem 2 := below 2 (by decide) (by decide) (by decide +kernel)
      with_unfolding_all change target.mem 2 = w[24] at oldAlias
      exact oldAlias
    have old : target.mem 16 = w[7] := by
      have oldPayload : target.mem 16 = indexed.machine.mem 16 := below 16 (by decide) (by decide) (by decide +kernel)
      with_unfolding_all change target.mem 16 = w[7] at oldPayload
      exact oldPayload
    let copy := (MVal.copyMToSt indexed.state.heap (T := .ref (R 1)) indexedReference).copyStToM indexed.state.heap rfl
    have item : (MObj.elems .fixed (copy.heap.get copy.val))[0]? = some (indexValue (wmod 7)) := by
      dsimp only [copy]
      rw [indexed_snapshot,fixed_primitive_source]
      with_unfolding_all rfl
    have contents : ReprV .uint (indexValue (wmod 7)) (target.mem ((base' copy.val.id).val + 0 + 0)) :=
      (allocated.heap.arrays .fixed copy.val).elements 0 (indexValue (wmod 7)) item
    obtain ⟨word,stored,equal⟩ := contents
    have same : word = wmod 7 := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    rw [root] at stored
    have payload : target.mem 40 = w[7] := stored
    with_unfolding_all change target.stack = [w[77]] at stack
    exact ⟨target,ran,cursor,localAt,alias,old,payload,stack⟩
  · rcases refused with badPath | ⟨_,_,noRoom⟩
    · rw [indexed_good] at badPath
      cases badPath
    · exact (noRoom indexed_fits).elim

private theorem indexed_bad : (indexedPath 2 rfl).mvalT indexed.state = .error .revert := by with_unfolding_all rfl
theorem indexed_refusal :
    (indexedPath 2 rfl).mvalT indexed.state = .error .revert ∧
    run ((indexedChosen 2 rfl).checkedFixedDeepBindCode indexed.destination) indexed.machine = .revert := by
  rcases (indexedChosen 2 rfl).checkedFixedDeepBindExecute indexed.represented indexed.allocator (by decide)
      indexed.destination with ⟨reference,evaluated,_⟩ | failed
  · rw [indexed_bad] at evaluated
    cases evaluated
  · exact ⟨indexed_bad,failed.2⟩

#print axioms certificate_inhabited
#print axioms actual_binding
#print axioms pair_binding
#print axioms empty_binding
#print axioms long_binding
#print axioms alias_source
#print axioms alias_target
#print axioms intrinsic_other_alias
#print axioms old_pointer_rejected
#print axioms header_rejected
#print axioms indexed_binding
#print axioms indexed_refusal

private def saturated (payloads : List (Fin W)) : Machine := writeMachine (machine payloads) 0 (.val wMax)
private theorem saturated_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.StateRepr 128 1 8 (Frag.init (Γ payloads.length)) (state payloads) bases (saturated payloads) := by
  have initial : Objects.StateRepr 128 1 8 (Frag.init (Γ payloads.length)) (state payloads) bases (machine payloads) := represented payloads bounded
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
    Objects.AllocatorRepr (heap payloads) bases 8 wMax (saturated payloads) := by
  have initial : Objects.AllocatorRepr (heap payloads) bases 8 (wmod 256) (machine payloads) := allocator payloads bounded
  have high : 256 ≤ wMax.val := by decide
  refine ⟨initial.heap.localWrite 0 (by decide) (.val wMax),⟨by decide,by omega,?_,?_⟩,?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (initial.free.zero address (by change 256 ≤ address; omega))
  · intro Q reference
    have live : (bases reference.id).val + Objects.cells (heap payloads) reference ≤ 256 := initial.live reference
    exact Nat.le_trans live high

theorem saturated_input (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.StateRepr 128 1 8 (Frag.init (Γ payloads.length)) (state payloads) bases (saturated payloads) ∧
    Objects.AllocatorRepr (heap payloads) bases 8 wMax (saturated payloads) :=
  ⟨saturated_repr payloads bounded,saturated_allocator payloads bounded⟩

theorem capacity_refusal (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (path payloads.length).mvalT (state payloads) = .ok (old payloads.length) ∧
    ¬ wMax.val + max 1 payloads.length < W ∧
    run (chosen payloads.length).checkedFixedDeepCode (saturated payloads) = .revert ∧
    run ((chosen payloads.length).checkedFixedDeepBindCode (destination payloads.length)) (saturated payloads) = .revert := by
  have nofit : ¬ wMax.val + max 1 payloads.length < W := by
    change ¬ (W - 1 + max 1 payloads.length < W)
    have positive : 0 < W := W_pos
    omega
  refine ⟨resolved payloads,nofit,?_,?_⟩
  · rcases (chosen payloads.length).checkedFixedDeepExecute (saturated_repr payloads bounded)
      (saturated_allocator payloads bounded) (by decide) with ⟨reference,evaluated,fits,_⟩ | failed
    · exact (nofit fits).elim
    · exact failed.2
  · rcases (chosen payloads.length).checkedFixedDeepBindExecute (saturated_repr payloads bounded)
      (saturated_allocator payloads bounded) (by decide) (destination payloads.length) with ⟨reference,evaluated,fits,_⟩ | failed
    · exact (nofit fits).elim
    · exact failed.2

theorem empty_capacity_refusal :
    run (chosen 0).checkedFixedDeepCode (saturated []) = .revert ∧
    run ((chosen 0).checkedFixedDeepBindCode (destination 0)) (saturated []) = .revert :=
  (capacity_refusal [] (by decide)).2.2

private def indexedSaturated : Machine := writeMachine indexed.machine 0 (.val wMax)
private theorem indexed_saturated_repr : Objects.StateRepr 1 1 8 indexed.frag indexed.state indexed.base indexedSaturated := by
  have initial : Objects.StateRepr 1 1 8 indexed.frag indexed.state indexed.base indexed.machine := indexed.represented
  refine ⟨initial.core.congrMem ?_,initial.heap.localWrite 0 (by decide) (.val wMax),?_,initial.locals⟩
  · intro level lower upper
    exact upd_other _ _ (by change level ≠ 0; omega)
  · intro Q index
    obtain ⟨reference,found,word⟩ := initial.pointers index
    refine ⟨reference,found,?_⟩
    change upd indexed.machine.mem 0 (.val wMax) (cellOf 1 index) = _
    rw [upd_other _ _ (by have lower : 1 ≤ lvl 1 index := le_lvl 1 index; change lvl 1 index ≠ 0; omega)]
    exact word
private theorem indexed_saturated_allocator : Objects.AllocatorRepr indexed.state.heap indexed.base 8 wMax indexedSaturated := by
  have initial : Objects.AllocatorRepr indexed.state.heap indexed.base 8 (wmod 40) indexed.machine := indexed.allocator
  have high : 40 ≤ wMax.val := by decide
  refine ⟨initial.heap.localWrite 0 (by decide) (.val wMax),⟨by decide,by omega,?_,?_⟩,?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (initial.free.zero address (by change 40 ≤ address; omega))
  · intro Q reference
    have live : (indexed.base reference.id).val + Objects.cells indexed.state.heap reference ≤ 40 := initial.live reference
    exact Nat.le_trans live high

theorem indexed_saturated_input :
    Objects.StateRepr 1 1 8 indexed.frag indexed.state indexed.base indexedSaturated ∧
    Objects.AllocatorRepr indexed.state.heap indexed.base 8 wMax indexedSaturated :=
  ⟨indexed_saturated_repr,indexed_saturated_allocator⟩

theorem bounds_before_capacity :
    (indexedPath 2 rfl).mvalT indexed.state = .error .revert ∧ indexedSaturated.mem 0 = .val wMax ∧
    run ((indexedChosen 2 rfl).checkedFixedDeepBindCode indexed.destination) indexedSaturated = .revert := by
  rcases (indexedChosen 2 rfl).checkedFixedDeepBindExecute indexed_saturated_repr indexed_saturated_allocator
      (by decide) indexed.destination with ⟨reference,evaluated,_⟩ | failed
  · rw [indexed_bad] at evaluated
    cases evaluated
  · exact ⟨indexed_bad,rfl,failed.2⟩

#print axioms saturated_input
#print axioms capacity_refusal
#print axioms empty_capacity_refusal
#print axioms indexed_saturated_input
#print axioms bounds_before_capacity
end Solidity.Backend.MemoryCopies.CheckedFixedPathCopyControls
