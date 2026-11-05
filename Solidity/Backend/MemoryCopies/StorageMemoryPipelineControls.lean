import Solidity.Backend.MemoryCopies.StorageMemoryPipeline
import Solidity.Evm.MemoryObjectArrayExamples

/-! The identical runtime code reads actual lengths0/2/64 and nonzero payloads
on a represented old heap. Room predicates are distinct from panic/gas semantics. -/
namespace Solidity.Backend.MemoryCopies.StorageMemoryPipelineControls
open Evm Evm.Memory
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,ObjectArrayExamples.initial_allocator⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 128 < W := by decide
private theorem large_bound : 512 < W := by decide
private theorem boundary_large : 1024 < W := by decide
private def value (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref (.array (.prim .uint))) :=
  primitiveArrayValue .uint (values payloads) (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide)
private def source : Slot := .root 0
private def store (payloads : List (Fin W)) : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod payloads.length
  | .data (.root 0) index => payloads[index]?.getD (wmod 0)
  | _ => wmod 0⟩
private def machine (payloads : List (Fin W)) : Machine := {input.machine with store := store payloads}
private def grown (payloads : List (Fin W)) (bounded : payloads.length < 128) :=
  (value payloads bounded).copyStToM input.heap rfl
private theorem represented (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprAt (machine payloads).store 128 (.ref (.array (.prim .uint))) source (value payloads bounded) := by
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
      simp only [machine,store,source,chosen,Option.getD_some]
      rfl
private theorem allocator (payloads : List (Fin W)) :
    Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (machine payloads) := input.allocator.mem_eq rfl

theorem certificate_inhabited : StorageMemoryPipelineCertificate := storageMemoryPipeline

theorem actual_typed (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ∃ fits, StorageMemoryPipelineResult input.heap .uint (values payloads)
      (by rw [values, List.length_map]; exact Nat.lt_trans bounded wide)
      input.base 8 (wmod 40) (machine payloads) source fits := by
  have fits : (wmod 40).val + 2 * ((values payloads).length + 1) < W := by
    change 40 + 2 * ((values payloads).length + 1) < W
    rw [values, List.length_map]
    have large : 512 < W := by decide
    omega
  exact ⟨fits, storage_memory_pipeline_success input.heap .uint (values payloads) _ input.base 8 (wmod 40)
    (machine payloads) source 128 (allocator payloads) (represented payloads bounded) fits⟩

private theorem observe_copy {H : HTy} (heap : Heap H) (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (base : Nat → Fin W) (cursor address : Fin W) (target : Machine)
    (allocated : Objects.AllocatorRepr ((value payloads bounded).copyStToM heap rfl).heap base 8 cursor target)
    (root : base ((value payloads bounded).copyStToM heap rfl).val.id = address) :
    target.mem address.val = .val (wmod payloads.length) ∧
    (∀ index payload, payloads[index]? = some payload → target.mem (address.val + 1 + index) = .val payload) := by
  let copied := (value payloads bounded).copyStToM heap rfl
  have length : copied.heap.len copied.val .dyn = payloads.length := by
    simpa only [value, values, List.length_map] using pipeline_first_length heap .uint (values payloads) _
  have header : target.mem (base copied.val.id).val = .val (wmod payloads.length) := by
    rw [(allocated.heap.arrays .dyn copied.val).length rfl, length]
  refine ⟨by rw [root] at header; exact header, ?_⟩
  intro index payload selected
  have item : (MObj.elems .dyn (copied.heap.get copied.val))[index]? = some (indexValue payload) := by
    dsimp only [copied, value]
    rw [primitive_array_source]
    simp only [Grown.alloc, Heap.get_alloc, MObj.elems_dyn, MObj.wk, primitiveArrayObject, MVal.wk, values,
      List.getElem?_map, selected, Option.map_some]
  have stored : ReprV .uint (indexValue payload) (target.mem ((base copied.val.id).val + 1 + index)) :=
    (allocated.heap.arrays .dyn copied.val).elements index (indexValue payload) item
  obtain ⟨word, equation, equal⟩ := stored
  have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
  subst word
  rw [root] at equation
  exact equation

theorem actual_runtime (payloads : List (Fin W)) (bounded : payloads.length < 128) : ∃ target : Machine,
    run storageMemoryPipelineCode ((machine payloads).push (.slot source)) =
      .ok (target.push (.val (wmod (40 + payloads.length + 1)))) 0 ∧
    target.mem 0 = .val (wmod (40 + 2 * (payloads.length + 1))) ∧
    target.mem 40 = .val (wmod payloads.length) ∧
    target.mem (40 + payloads.length + 1) = .val (wmod payloads.length) ∧
    target.mem 17 = w[7] ∧ target.stack = [w[77]] ∧ target.store = (machine payloads).store ∧
    (∀ index payload, payloads[index]? = some payload →
      target.mem (41 + index) = .val payload ∧ target.mem (40 + payloads.length + 2 + index) = .val payload) := by
  obtain ⟨fits, firstFits, base₁, intermediate, base₂, target, firstRun, firstAllocator, firstRoot, wholeRun,
    finalAllocator, finalRoot, retainedRoot, extension, shape, below, retained, gaps, keptOld, keptFirst, fresh, firstContents, secondContents⟩ :=
    actual_typed payloads bounded
  let first := grown payloads bounded
  let second := (value payloads bounded).copyStToM first.heap rfl
  have snapshot : MVal.copyMToSt first.heap first.val = value payloads bounded :=
    pipeline_first_snapshot input.heap .uint (values payloads) _
  change Objects.AllocatorRepr ((MVal.copyMToSt first.heap first.val).copyStToM first.heap rfl).heap base₂ 8 _ target at finalAllocator
  change base₂ ((MVal.copyMToSt first.heap first.val).copyStToM first.heap rfl).val.id = _ at finalRoot
  rw [snapshot] at finalAllocator finalRoot
  have allocated : Objects.AllocatorRepr second.heap base₂ 8
      ⟨(wmod 40).val + 2 * ((values payloads).length + 1), fits⟩ target := by
    exact finalAllocator
  have root : base₂ second.val.id = ⟨(wmod 40).val + ((values payloads).length + 1), firstFits⟩ := by
    exact finalRoot
  have pointer : (⟨(wmod 40).val + ((values payloads).length + 1), firstFits⟩ : Fin W) = wmod (40 + payloads.length + 1) := by
    apply Fin.ext
    simp only [values, List.length_map]
    change 40 + (payloads.length + 1) = (40 + payloads.length + 1) % W
    have bound : 40 + payloads.length + 1 < W := by have large : 512 < W := large_bound; omega
    rw [Nat.mod_eq_of_lt bound]
    omega
  have firstObserved : intermediate.mem (wmod 40).val = .val (wmod payloads.length) ∧
      (∀ index payload, payloads[index]? = some payload → intermediate.mem ((wmod 40).val + 1 + index) = .val payload) := observe_copy input.heap payloads bounded base₁ _ (wmod 40) intermediate firstAllocator firstRoot
  have secondObserved : target.mem (wmod (40 + payloads.length + 1)).val = .val (wmod payloads.length) ∧
      (∀ index payload, payloads[index]? = some payload → target.mem ((wmod (40 + payloads.length + 1)).val + 1 + index) = .val payload) := observe_copy first.heap payloads bounded base₂ _ (wmod (40 + payloads.length + 1)) target allocated (root.trans pointer)
  refine ⟨target, ?_, ?_, ?_, ?_, (below 17 (by decide) (by decide)).trans rfl, ?_, ?_, ?_⟩
  · rw [pointer] at wholeRun
    exact wholeRun
  · refine allocated.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    simp only [values, List.length_map]
    change 40 + 2 * (payloads.length + 1) = (40 + 2 * (payloads.length + 1)) % W
    exact (Nat.mod_eq_of_lt (by have large : 512 < W := large_bound; omega)).symm
  · exact (retained 40 (by decide) (by change 40 < 40 + ((values payloads).length + 1); omega)).trans firstObserved.1
  · have bound : 40 + payloads.length + 1 < W := by have large : 512 < W := large_bound; omega
    simpa only [wmod_def, Nat.mod_eq_of_lt bound] using secondObserved.1
  · exact congrArg Machine.stack shape
  · rw [shape]
  · intro index payload chosen
    have lower : index < payloads.length := lt_of_getElem? chosen
    have firstWord : intermediate.mem ((wmod 40).val + 1 + index) = .val payload := firstObserved.2 index payload chosen
    have secondWord : target.mem ((wmod (40 + payloads.length + 1)).val + 1 + index) = .val payload := secondObserved.2 index payload chosen
    have bound : 40 + payloads.length + 1 < W := by have large : 512 < W := large_bound; omega
    refine ⟨(retained (41 + index) (by omega) (by simp only [values, List.length_map]; change 41 + index < 40 + (payloads.length + 1); omega)).trans firstWord, ?_⟩
    change target.mem ((40 + payloads.length + 1) % W + 1 + index) = .val payload at secondWord
    rw [Nat.mod_eq_of_lt bound] at secondWord
    have address : 40 + payloads.length + 1 + 1 + index = 40 + payloads.length + 2 + index := by omega
    rw [address] at secondWord
    exact secondWord

theorem empty_runtime : ∃ target : Machine,
    run storageMemoryPipelineCode ((machine []).push (.slot source)) = .ok (target.push w[41]) 0 ∧
    target.mem 0 = w[42] ∧ target.mem 40 = w[0] ∧ target.mem 41 = w[0] ∧ target.mem 17 = w[7] := by
  obtain ⟨target, ran, cursor, first, second, old, _⟩ := actual_runtime [] (by decide)
  exact ⟨target, ran, cursor, first, second, old⟩

theorem pair_runtime : ∃ target : Machine,
    run storageMemoryPipelineCode ((machine [wmod 11, wmod 23]).push (.slot source)) = .ok (target.push w[43]) 0 ∧
    target.mem 0 = w[46] ∧ target.mem 40 = w[2] ∧ target.mem 43 = w[2] ∧
    target.mem 41 = w[11] ∧ target.mem 42 = w[23] ∧ target.mem 44 = w[11] ∧ target.mem 45 = w[23] ∧ target.mem 17 = w[7] := by
  obtain ⟨target, ran, cursor, first, second, old, _, _, words⟩ := actual_runtime [wmod 11, wmod 23] (by decide)
  exact ⟨target, ran, cursor, first, second, (words 0 (wmod 11) rfl).1, (words 1 (wmod 23) rfl).1,
    (words 0 (wmod 11) rfl).2, (words 1 (wmod 23) rfl).2, old⟩

private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))
theorem long_runtime : ∃ target : Machine,
    run storageMemoryPipelineCode ((machine long).push (.slot source)) = .ok (target.push w[105]) 0 ∧
    target.mem 0 = w[170] ∧ target.mem 40 = w[64] ∧ target.mem 105 = w[64] ∧
    target.mem 41 = w[1] ∧ target.mem 104 = w[64] ∧ target.mem 106 = w[1] ∧ target.mem 169 = w[64] := by
  obtain ⟨target, ran, cursor, first, second, _, _, _, words⟩ := actual_runtime long (by rw [long, List.length_ofFn]; decide)
  simpa only [long, List.length_ofFn] using
    ⟨target, ran, cursor, first, second, (words 0 (wmod 1) (by decide +kernel)).1,
      (words 63 (wmod 64) (by decide +kernel)).1, (words 0 (wmod 1) (by decide +kernel)).2,
      (words 63 (wmod 64) (by decide +kernel)).2⟩

private def moved (payloads : List (Fin W)) (cursor : Fin W) : Machine := writeMachine (machine payloads) 0 (.val cursor)
private theorem moved_allocator (payloads : List (Fin W)) (cursor : Fin W) (above : 40 ≤ cursor.val) :
    Objects.AllocatorRepr input.heap input.base 8 cursor (moved payloads cursor) := by
  have initial : Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (machine payloads) := allocator payloads
  refine ⟨initial.heap.localWrite 0 (by decide) (.val cursor),⟨by decide,by omega,?_,?_⟩,?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (initial.free.zero address (by change 40 ≤ address; omega))
  · intro Q reference
    have live : (input.base reference.id).val + Objects.cells input.heap reference ≤ 40 := initial.live reference
    omega
private theorem moved_representation (payloads : List (Fin W)) (bounded : payloads.length < 128) (cursor : Fin W) :
    ReprAt (moved payloads cursor).store 128 (.ref (.array (.prim .uint))) source (value payloads bounded) :=
  represented payloads bounded

theorem first_phase_refusal (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    run checkedStorageArrayCode ((moved payloads wMax).push (.slot source)) = .revert ∧
    run storageMemoryPipelineCode ((moved payloads wMax).push (.slot source)) = .revert := by
  have firstRun : run checkedStorageArrayCode ((moved payloads wMax).push (.slot source)) = .revert := by
    rw [checked_storage_array_run input.heap .uint (values payloads) _ input.base 8 wMax (moved payloads wMax) source 128
      (moved_allocator payloads wMax (by decide)) (moved_representation payloads bounded wMax)]
    apply if_neg
    change ¬ (W - 1 + ((values payloads).length + 1) < W)
    have positive : 0 < W := W_pos
    omega
  exact ⟨firstRun, run_append_revert firstRun⟩

theorem second_phase_refusal (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (cursor : Fin W) (above : 40 ≤ cursor.val)
    (firstFits : cursor.val + ((values payloads).length + 1) < W)
    (tooLarge : ¬ cursor.val + 2 * ((values payloads).length + 1) < W) :
    (∃ (firstFits : cursor.val + ((values payloads).length + 1) < W), ∃ base₁ intermediate,
      run checkedStorageArrayCode ((moved payloads cursor).push (.slot source)) = .ok (intermediate.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr (grown payloads bounded).heap base₁ 8
        ⟨cursor.val + ((values payloads).length + 1), firstFits⟩ intermediate ∧
      run checkedMemoryArrayCode (intermediate.push (.val cursor)) = .revert) ∧
    run storageMemoryPipelineCode ((moved payloads cursor).push (.slot source)) = .revert := by
  obtain ⟨reason, wholeRun⟩ := storage_memory_pipeline_refusal input.heap .uint (values payloads) _ input.base 8 cursor
    (moved payloads cursor) source 128 (moved_allocator payloads cursor above) (moved_representation payloads bounded cursor) tooLarge
  rcases reason with ⟨impossible, _⟩ | ⟨firstFits, base₁, intermediate, firstRun, allocated, _, _, _, secondRun⟩
  · exact (impossible firstFits).elim
  · exact ⟨⟨firstFits, base₁, intermediate, firstRun, allocated, secondRun⟩, wholeRun⟩

private theorem boundary_value (n : Nat) (positive : 0 < n) (bounded : n ≤ 512) :
    (wmod (W - n)).val = W - n ∧ 40 ≤ (wmod (W - n)).val := by
  have large : 1024 < W := by decide
  have bound : W - n < W := by omega
  change (W - n) % W = W - n ∧ 40 ≤ (W - n) % W
  rw [Nat.mod_eq_of_lt bound]
  omega

theorem empty_second_refusal :
    (∃ firstFits base₁ intermediate,
      run checkedStorageArrayCode ((moved [] (wmod (W - 2))).push (.slot source)) = .ok (intermediate.push (.val (wmod (W - 2)))) 0 ∧
      Objects.AllocatorRepr (grown [] (by decide)).heap base₁ 8 ⟨(wmod (W - 2)).val + 1, firstFits⟩ intermediate ∧
      run checkedMemoryArrayCode (intermediate.push (.val (wmod (W - 2)))) = .revert) ∧
    run storageMemoryPipelineCode ((moved [] (wmod (W - 2))).push (.slot source)) = .revert := by
  have edge : (wmod (W - 2)).val = W - 2 ∧ 40 ≤ (wmod (W - 2)).val := boundary_value 2 (by decide) (by decide)
  exact second_phase_refusal [] (by decide) _ edge.2 (by rw [edge.1]; change W - 2 + 1 < W; have large : 1024 < W := boundary_large; omega)
    (by rw [edge.1]; change ¬ W - 2 + 2 * (0 + 1) < W; have large : 1024 < W := boundary_large; omega)

theorem pair_second_refusal :
    (∃ (firstFits : (wmod (W - 4)).val + 3 < W), ∃ base₁ intermediate,
      run checkedStorageArrayCode ((moved [wmod 11, wmod 23] (wmod (W - 4))).push (.slot source)) =
        .ok (intermediate.push (.val (wmod (W - 4)))) 0 ∧
      Objects.AllocatorRepr (grown [wmod 11, wmod 23] (by decide)).heap base₁ 8
        ⟨(wmod (W - 4)).val + 3, firstFits⟩ intermediate ∧
      run checkedMemoryArrayCode (intermediate.push (.val (wmod (W - 4)))) = .revert) ∧
    run storageMemoryPipelineCode ((moved [wmod 11, wmod 23] (wmod (W - 4))).push (.slot source)) = .revert := by
  have edge : (wmod (W - 4)).val = W - 4 ∧ 40 ≤ (wmod (W - 4)).val := boundary_value 4 (by decide) (by decide)
  exact second_phase_refusal [wmod 11, wmod 23] (by decide) _ edge.2
    (by rw [edge.1]; change W - 4 + 3 < W; have large : 1024 < W := boundary_large; omega)
    (by rw [edge.1]; change ¬ W - 4 + 2 * (2 + 1) < W; have large : 1024 < W := boundary_large; omega)

theorem pair_last_fitting : ∃ fits, StorageMemoryPipelineResult input.heap .uint (values [wmod 11, wmod 23]) (by decide)
    input.base 8 (wmod (W - 7)) (moved [wmod 11, wmod 23] (wmod (W - 7))) source fits := by
  have edge : (wmod (W - 7)).val = W - 7 ∧ 40 ≤ (wmod (W - 7)).val := boundary_value 7 (by decide) (by decide)
  have fits : (wmod (W - 7)).val + 2 * ((values [wmod 11, wmod 23]).length + 1) < W := by
    rw [edge.1]
    change W - 7 + 2 * (2 + 1) < W
    have large : 1024 < W := by decide
    omega
  exact ⟨fits, storage_memory_pipeline_success input.heap .uint _ (by decide) input.base 8 _ _ source 128
    (moved_allocator _ _ edge.2) (moved_representation _ (by decide) _) fits⟩

theorem wrong_payload (target : Machine)
    (ran : run storageMemoryPipelineCode ((machine [wmod 11, wmod 23]).push (.slot source)) = .ok (target.push w[43]) 0) :
    target.mem 42 ≠ w[0] ∧ target.mem 45 ≠ w[0] := by
  obtain ⟨actual, execution, _, _, _, _, first, _, second, _⟩ := pair_runtime
  rw [ran] at execution
  have same : (target.push w[43]).mem = (actual.push w[43]).mem := congrArg (fun m : Machine => m.mem) (Out.ok.inj execution).1
  change target.mem = actual.mem at same
  rw [same, first, second]
  decide

theorem wrong_alias : ¬ ∃ target : Machine,
    run storageMemoryPipelineCode ((machine [wmod 11, wmod 23]).push (.slot source)) = .ok (target.push w[40]) 0 := by
  obtain ⟨actual, execution, _⟩ := pair_runtime
  rintro ⟨target, proposed⟩
  rw [proposed] at execution
  have heads : (target.push w[40]).stack.head? = (actual.push w[43]).stack.head? :=
    congrArg (fun m : Machine => m.stack.head?) (Out.ok.inj execution).1
  have different : (some w[40] : Option Word) ≠ some w[43] := by decide
  exact different heads

#print axioms certificate_inhabited
#print axioms actual_typed
#print axioms actual_runtime
#print axioms empty_runtime
#print axioms pair_runtime
#print axioms long_runtime
#print axioms first_phase_refusal
#print axioms second_phase_refusal
#print axioms empty_second_refusal
#print axioms pair_second_refusal
#print axioms pair_last_fitting
#print axioms wrong_payload
#print axioms wrong_alias
end Solidity.Backend.MemoryCopies.StorageMemoryPipelineControls
