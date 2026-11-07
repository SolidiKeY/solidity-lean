import Solidity.Backend.MemoryCopies.NestedMemoryTurn
import Solidity.Backend.MemoryCopies.StorageMemoryPipeline

/-! A real dynamic parent contains two aliases of the same variable-length
child. A separate reservation receives the new deep-copy pointer. -/
namespace Solidity.Backend.MemoryCopies.NestedMemoryTurnControls
open Evm Evm.Memory
private abbrev R : RefTy := .array (.prim .uint)
private abbrev P : RefTy := .array (.ref R)
private abbrev H : HTy := [R, P]
private def child : HRef H R := ⟨0, rfl⟩
private def source : HRef H P := ⟨1, rfl⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 128 < W := by decide
private def heap (payloads : List (Fin W)) (bounded : payloads.length < 128) : Heap H :=
  (⟨values payloads, by rw [values, List.length_map]; have large : 128 < W := wide; omega⟩, (⟨[child,child], by decide⟩, ()))
private def base (identity : Nat) : Fin W := if identity = 0 then wmod 16 else wmod 160
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with stack := [w[77]], mem := fun address =>
    if address = 0 then w[192] else if address = 7 then w[99]
    else if address = 16 then .val (wmod payloads.length) else if address = 160 then w[2]
    else if address = 161 ∨ address = 162 then w[16]
    else if 17 ≤ address ∧ address < 17 + payloads.length then .val (payloads[address - 17]?.getD (wmod 0)) else w[0]}
private theorem refs {Q : RefTy} (reference : HRef H Q) : (Q = R ∧ HEq reference child) ∨ (Q = P ∧ HEq reference source) := by
  rcases reference with ⟨index, selected⟩
  cases index with
  | zero => cases selected; exact .inl ⟨rfl, HEq.rfl⟩
  | succ index => cases index with
    | zero => cases selected; exact .inr ⟨rfl, HEq.rfl⟩
    | succ index => cases selected
private theorem cells_child (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.cells (heap payloads bounded) child = 1 + payloads.length := by
  with_unfolding_all change 1 + (values payloads).length = 1 + payloads.length
  rw [values, List.length_map]
private theorem cells_source (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.cells (heap payloads bounded) source = 3 := by
  with_unfolding_all rfl
private theorem heap_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.HeapRepr (heap payloads bounded) base 8 (machine payloads) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro Q reference
    rcases refs reference with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq <;> decide
  · intro Q reference
    rcases refs reference with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq
    · rw [cells_child]
      change 16 + (1 + payloads.length) ≤ W
      have large : 512 < W := by decide
      omega
    · rw [cells_source]
      decide
  · intro Q S left right different
    rcases refs left with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq
      <;> rcases refs right with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq
    · exact (different rfl).elim
    · left
      rw [cells_child]
      change 16 + (1 + payloads.length) ≤ 160
      omega
    · right
      rw [cells_child]
      change 16 + (1 + payloads.length) ≤ 160
      omega
    · exact (different rfl).elim
  · intro A E shape reference
    rcases refs reference with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq <;> cases shape
    · refine ⟨?_, ?_, ?_⟩
      · rw [cells_child]
        change 16 + (1 + payloads.length) ≤ W
        have large : 512 < W := by decide
        omega
      · intro _
        with_unfolding_all change Word.val (wmod payloads.length) = Word.val (wmod (values payloads).length)
        rw [values, List.length_map]
      · intro index item selected
        with_unfolding_all change (values payloads)[index]? = some item at selected
        simp only [values, List.getElem?_map] at selected
        cases found : payloads[index]? with
        | none => simp only [found, Option.map_none] at selected; cases selected
        | some payload =>
          simp only [found, Option.map_some] at selected
          cases selected
          have lower : index < payloads.length := lt_of_getElem? found
          change ReprV .uint (indexValue payload) ((machine payloads).mem (17 + index))
          simp only [machine, if_neg (show 17 + index ≠ 0 by omega), if_neg (show 17 + index ≠ 7 by omega),
            if_neg (show 17 + index ≠ 16 by omega), if_neg (show 17 + index ≠ 160 by omega),
            if_neg (show ¬(17 + index = 161 ∨ 17 + index = 162) by omega),
            if_pos (show 17 ≤ 17 + index ∧ 17 + index < 17 + payloads.length by omega), Nat.add_sub_cancel_left, found, Option.getD_some]
          exact ReprV.uint_of rfl
    · refine ⟨by rw [cells_source]; decide, ?_, ?_⟩
      · intro _
        with_unfolding_all rfl
      · intro index item selected
        with_unfolding_all change [child,child][index]? = some item at selected
        cases index with
        | zero => cases selected; rfl
        | succ index => cases index with
          | zero => cases selected; rfl
          | succ index => cases selected
  · intro name reference
    rcases refs reference with ⟨different, _⟩ | ⟨different, _⟩ <;> cases different
  · intro name field Q reference fieldType
    rcases refs reference with ⟨different, _⟩ | ⟨different, _⟩ <;> cases different
private theorem allocator (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.AllocatorRepr (heap payloads bounded) base 8 (wmod 192) (machine payloads) := by
  refine ⟨heap_repr payloads bounded, ⟨by decide, by decide, rfl, ?_⟩, ?_⟩
  · intro address above
    change 192 ≤ address at above
    simp only [machine, if_neg (show address ≠ 0 by omega), if_neg (show address ≠ 7 by omega),
      if_neg (show address ≠ 16 by omega), if_neg (show address ≠ 160 by omega),
      if_neg (show ¬(address = 161 ∨ address = 162) by omega), if_neg (show ¬(17 ≤ address ∧ address < 17 + payloads.length) by omega)]
  · intro Q reference
    rcases refs reference with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq
    · rw [cells_child]
      change 16 + (1 + payloads.length) ≤ 192
      omega
    · rw [cells_source]
      decide
private def reserved (payloads : List (Fin W)) : Machine := allocateMachine (machine payloads) (wmod 192) (wmod 3)
private theorem reservation (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.AllocatorRepr (heap payloads bounded) base 8 (wmod 196) (reserved payloads) ∧
      Objects.Gap (heap payloads bounded) base 192 196 :=
  (allocator payloads bounded).reserveArray (wmod 3) (by decide)

theorem certificate_inhabited : NestedMemoryTurnCertificate := nestedMemoryTurn

theorem shared_source (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (heap payloads bounded).index source .dyn (indexValue (wmod 0)) = some child ∧
    (heap payloads bounded).index source .dyn (indexValue (wmod 1)) = some child := by
  exact ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

theorem actual_typed (payloads : List (Fin W)) (bounded : payloads.length < 128) (selected : Fin 2) :
    ∃ fits, NestedMemoryTurnResult (heap payloads bounded) .uint source child base 8 (wmod 196) (reserved payloads)
      (wmod 192) (wmod 3) ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩ fits := by
  have chosen : (heap payloads bounded).index source .dyn (indexValue ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩) = some child := by
    cases selected with | mk n lower => cases n with
      | zero => with_unfolding_all rfl
      | succ n => cases n with
        | zero => with_unfolding_all rfl
        | succ n => omega
  have length : (heap payloads bounded).len child .dyn = payloads.length := by
    with_unfolding_all change (values payloads).length = payloads.length
    rw [values, List.length_map]
  have fits : (wmod 196).val + ((heap payloads bounded).len child .dyn + 1) < W := by
    rw [length]
    change 196 + (payloads.length + 1) < W
    have large : 512 < W := by decide
    omega
  exact ⟨fits, nested_memory_turn_success (heap payloads bounded) .uint source child base 8 (wmod 196) (reserved payloads)
    (wmod 192) (wmod 3) _ (reservation payloads bounded).1 (reservation payloads bounded).2 (by decide) (by decide)
    (by change selected.val < 3; omega) chosen fits⟩

private def value (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref R) :=
  primitiveArrayValue .uint (values payloads) (by rw [values, List.length_map]; exact Nat.lt_trans bounded wide)
private theorem source_snapshot (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    MVal.copyMToSt (heap payloads bounded) (T := .ref R) child = value payloads bounded := by
  rw [primitiveArray_snapshot]
  with_unfolding_all rfl

theorem actual_runtime (payloads : List (Fin W)) (bounded : payloads.length < 128) (selected : Fin 2) : ∃ target : Machine,
    run (nestedMemoryTurnCode .uint)
      (nestedMemoryControl (reserved payloads) (wmod 160) (wmod 192) (wmod 3) ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 3) (wmod (selected.val + 1))) 0 ∧
    target.mem (193 + selected.val) = w[196] ∧ target.mem 161 = w[16] ∧ target.mem 162 = w[16] ∧
    target.mem 0 = .val (wmod (197 + payloads.length)) ∧ target.mem 196 = .val (wmod payloads.length) ∧
    (∀ index payload, payloads[index]? = some payload → target.mem (17 + index) = .val payload ∧ target.mem (197 + index) = .val payload) := by
  obtain ⟨fits, base', target, ran, allocated, root, extension, gap, stored, shape, below, gaps, keeps, fresh, contents⟩ :=
    actual_typed payloads bounded selected
  let copied := (value payloads bounded).copyStToM (heap payloads bounded) rfl
  change Objects.AllocatorRepr ((MVal.copyMToSt (heap payloads bounded) (T := .ref R) child).copyStToM (heap payloads bounded) rfl).heap base' 8 _ target at allocated
  change base' ((MVal.copyMToSt (heap payloads bounded) (T := .ref R) child).copyStToM (heap payloads bounded) rfl).val.id = _ at root
  rw [source_snapshot] at allocated root
  have length : copied.heap.len copied.val .dyn = payloads.length := by
    simpa only [value, values, List.length_map] using pipeline_first_length (heap payloads bounded) .uint (values payloads) _
  have header : target.mem 196 = .val (wmod payloads.length) := by
    have actual : target.mem (base' copied.val.id).val = .val (wmod (copied.heap.len copied.val .dyn)) :=
      (allocated.heap.arrays .dyn copied.val).length rfl
    rw [root, length] at actual
    exact actual
  have sourceLength : (heap payloads bounded).len child .dyn = payloads.length := by
    with_unfolding_all change (values payloads).length = payloads.length
    rw [values, List.length_map]
  refine ⟨target, ran, stored, ?_, ?_, ?_, header, ?_⟩
  · exact (below 161 (by decide) (by decide) (by change 161 ≠ 193 + selected.val; omega)).trans (by with_unfolding_all rfl)
  · exact (below 162 (by decide) (by decide) (by change 162 ≠ 193 + selected.val; omega)).trans (by with_unfolding_all rfl)
  · refine allocated.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    change 196 + ((heap payloads bounded).len child .dyn + 1) = (197 + payloads.length) % W
    rw [sourceLength, Nat.mod_eq_of_lt (show 197 + payloads.length < W by have large : 512 < W := (by decide); omega)]
    omega
  · intro index payload chosen
    have lower : index < payloads.length := lt_of_getElem? chosen
    have old : (reserved payloads).mem (17 + index) = .val payload := by
      change upd (upd (machine payloads).mem 192 _) 0 _ (17 + index) = _
      rw [upd_other _ _ (by omega), upd_other _ _ (by omega)]
      simp only [machine, if_neg (show 17 + index ≠ 0 by omega), if_neg (show 17 + index ≠ 7 by omega),
        if_neg (show 17 + index ≠ 16 by omega), if_neg (show 17 + index ≠ 160 by omega),
        if_neg (show ¬(17 + index = 161 ∨ 17 + index = 162) by omega),
        if_pos (show 17 ≤ 17 + index ∧ 17 + index < 17 + payloads.length by omega), Nat.add_sub_cancel_left, chosen, Option.getD_some]
    have item : (MObj.elems .dyn (copied.heap.get copied.val))[index]? = some (indexValue payload) := by
      dsimp only [copied, value]
      rw [primitive_array_source]
      simp only [Grown.alloc, Heap.get_alloc, MObj.elems_dyn, MObj.wk, primitiveArrayObject, MVal.wk, values,
        List.getElem?_map, chosen, Option.map_some]
    have represented : ReprV .uint (indexValue payload) (target.mem ((base' copied.val.id).val + 1 + index)) :=
      (allocated.heap.arrays .dyn copied.val).elements index (indexValue payload) item
    obtain ⟨word, copiedWord, equal⟩ := represented
    have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    rw [root] at copiedWord
    exact ⟨(below (17 + index) (by omega) (by change 17 + index < 196; omega)
      (by change 17 + index ≠ 193 + selected.val; omega)).trans old, copiedWord⟩

theorem empty_runtime : ∃ target : Machine,
    run (nestedMemoryTurnCode .uint) (nestedMemoryControl (reserved []) (wmod 160) (wmod 192) (wmod 3) (wmod 1)) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 3) (wmod 2)) 0 ∧
    target.mem 194 = w[196] ∧ target.mem 161 = w[16] ∧ target.mem 162 = w[16] ∧ target.mem 0 = w[197] ∧ target.mem 196 = w[0] := by
  obtain ⟨target, ran, stored, left, right, cursor, header, _⟩ := actual_runtime [] (by decide) ⟨1, by decide⟩
  exact ⟨target, ran, stored, left, right, cursor, header⟩

theorem pair_runtime (selected : Fin 2) : ∃ target : Machine,
    run (nestedMemoryTurnCode .uint) (nestedMemoryControl (reserved [wmod 11, wmod 23]) (wmod 160) (wmod 192) (wmod 3)
      ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 3) (wmod (selected.val + 1))) 0 ∧
    target.mem (193 + selected.val) = w[196] ∧ target.mem 161 = w[16] ∧ target.mem 162 = w[16] ∧
    target.mem 17 = w[11] ∧ target.mem 18 = w[23] ∧ target.mem 197 = w[11] ∧ target.mem 198 = w[23] := by
  obtain ⟨target, ran, stored, left, right, _, _, words⟩ := actual_runtime [wmod 11, wmod 23] (by decide) selected
  exact ⟨target, ran, stored, left, right, (words 0 (wmod 11) rfl).1, (words 1 (wmod 23) rfl).1,
    (words 0 (wmod 11) rfl).2, (words 1 (wmod 23) rfl).2⟩

private def long : List (Fin W) := List.ofFn (fun i : Fin 64 => wmod (i.val + 1))
theorem long_runtime : ∃ target : Machine,
    run (nestedMemoryTurnCode .uint) (nestedMemoryControl (reserved long) (wmod 160) (wmod 192) (wmod 3) (wmod 0)) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 3) (wmod 1)) 0 ∧
    target.mem 193 = w[196] ∧ target.mem 161 = w[16] ∧ target.mem 162 = w[16] ∧ target.mem 0 = w[261] ∧
    target.mem 17 = w[1] ∧ target.mem 80 = w[64] ∧ target.mem 197 = w[1] ∧ target.mem 260 = w[64] := by
  obtain ⟨target, ran, stored, left, right, cursor, _, words⟩ := actual_runtime long (by rw [long, List.length_ofFn]; decide) ⟨0, by decide⟩
  exact ⟨target, ran, stored, left, right, by simpa only [long, List.length_ofFn] using cursor,
    (words 0 (wmod 1) (by decide +kernel)).1, (words 63 (wmod 64) (by decide +kernel)).1,
    (words 0 (wmod 1) (by decide +kernel)).2, (words 63 (wmod 64) (by decide +kernel)).2⟩
private def moved (payloads : List (Fin W)) (cursor : Fin W) : Machine := writeMachine (reserved payloads) 0 (.val cursor)
private theorem moved_allocator (payloads : List (Fin W)) (bounded : payloads.length < 128) (cursor : Fin W) (above : 196 ≤ cursor.val) :
    Objects.AllocatorRepr (heap payloads bounded) base 8 cursor (moved payloads cursor) := by
  have initial : Objects.AllocatorRepr (heap payloads bounded) base 8 (wmod 196) (reserved payloads) := (reservation payloads bounded).1
  refine ⟨initial.heap.localWrite 0 (by decide) (.val cursor), ⟨by decide, by omega, rfl, ?_⟩, ?_⟩
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (initial.free.zero address (by change 196 ≤ address; omega))
  · intro Q reference
    have live : (base reference.id).val + Objects.cells (heap payloads bounded) reference ≤ 196 := initial.live reference
    omega

theorem bounds_refusal (payloads : List (Fin W)) (bounded : payloads.length < 128) (cursor : Fin W) (above : 196 ≤ cursor.val) :
    (heap payloads bounded).index source .dyn (indexValue (wmod 2)) = none ∧
    run (nestedMemoryTurnCode .uint) (nestedMemoryControl (moved payloads cursor) (wmod 160) (wmod 192) (wmod 3) (wmod 2)) = .revert := by
  have absent : (heap payloads bounded).index source .dyn (indexValue (wmod 2)) = none := by with_unfolding_all rfl
  have before : (wmod 192).val + 1 + (wmod 3).val ≤ cursor.val := by change 196 ≤ cursor.val; exact above
  rcases nested_memory_turn_correct (heap payloads bounded) .uint source base 8 cursor (moved payloads cursor)
      (wmod 192) (wmod 3) (wmod 2) (moved_allocator payloads bounded cursor above) (reservation payloads bounded).2
      (by decide) before (by decide) with ⟨child, chosen, _, _⟩ | ⟨_, failed⟩
  · rw [absent] at chosen
    cases chosen
  · exact ⟨absent, failed⟩

theorem capacity_refusal (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (heap payloads bounded).index source .dyn (indexValue (wmod 0)) = some child ∧
    run (nestedMemoryTurnCode .uint) (nestedMemoryControl (moved payloads wMax) (wmod 160) (wmod 192) (wmod 3) (wmod 0)) = .revert := by
  have chosen : (heap payloads bounded).index source .dyn (indexValue (wmod 0)) = some child := (shared_source payloads bounded).1
  rcases nested_memory_turn_correct (heap payloads bounded) .uint source base 8 wMax (moved payloads wMax)
      (wmod 192) (wmod 3) (wmod 0) (moved_allocator payloads bounded wMax (by decide)) (reservation payloads bounded).2
      (by decide) (by decide) (by decide) with ⟨actual, found, fits, _⟩ | ⟨_, failed⟩
  · change W - 1 + ((heap payloads bounded).len actual .dyn + 1) < W at fits
    have positive : 0 < W := W_pos
    omega
  · exact ⟨chosen, failed⟩

theorem bounds_at_saturation :
    run (nestedMemoryTurnCode .uint) (nestedMemoryControl (moved [wmod 11, wmod 23] wMax) (wmod 160) (wmod 192) (wmod 3) (wmod 2)) = .revert :=
  (bounds_refusal [wmod 11, wmod 23] (by decide) wMax (by decide)).2

theorem wrong_alias (target : Machine)
    (ran : run (nestedMemoryTurnCode .uint) (nestedMemoryControl (reserved [wmod 11, wmod 23]) (wmod 160) (wmod 192) (wmod 3) (wmod 0)) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 3) (wmod 1)) 0) : target.mem 193 ≠ w[16] := by
  obtain ⟨actual, execution, stored, _⟩ := pair_runtime ⟨0, by decide⟩
  change run (nestedMemoryTurnCode .uint) (nestedMemoryControl (reserved [wmod 11, wmod 23]) (wmod 160) (wmod 192) (wmod 3) (wmod 0)) =
    .ok (nestedMemoryControl actual (wmod 160) (wmod 192) (wmod 3) (wmod 1)) 0 at execution
  rw [ran] at execution
  have same : (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 3) (wmod 1)).mem =
      (nestedMemoryControl actual (wmod 160) (wmod 192) (wmod 3) (wmod 1)).mem := congrArg (fun m : Machine => m.mem) (Out.ok.inj execution).1
  change target.mem = actual.mem at same
  change actual.mem 193 = w[196] at stored
  rw [same, stored]
  decide

theorem wrong_payload (target : Machine)
    (ran : run (nestedMemoryTurnCode .uint) (nestedMemoryControl (reserved [wmod 11, wmod 23]) (wmod 160) (wmod 192) (wmod 3) (wmod 0)) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 3) (wmod 1)) 0) : target.mem 198 ≠ w[0] ∧ target.mem 18 ≠ w[0] := by
  obtain ⟨actual, execution, _, _, _, _, old, _, copied⟩ := pair_runtime ⟨0, by decide⟩
  change run (nestedMemoryTurnCode .uint) (nestedMemoryControl (reserved [wmod 11, wmod 23]) (wmod 160) (wmod 192) (wmod 3) (wmod 0)) =
    .ok (nestedMemoryControl actual (wmod 160) (wmod 192) (wmod 3) (wmod 1)) 0 at execution
  rw [ran] at execution
  have same : (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 3) (wmod 1)).mem =
      (nestedMemoryControl actual (wmod 160) (wmod 192) (wmod 3) (wmod 1)).mem := congrArg (fun m : Machine => m.mem) (Out.ok.inj execution).1
  change target.mem = actual.mem at same
  rw [same, old, copied]
  decide
#print axioms certificate_inhabited
#print axioms shared_source
#print axioms actual_typed
#print axioms actual_runtime
#print axioms empty_runtime
#print axioms pair_runtime
#print axioms long_runtime
#print axioms bounds_refusal
#print axioms capacity_refusal
#print axioms bounds_at_saturation
#print axioms wrong_alias
#print axioms wrong_payload
end Solidity.Backend.MemoryCopies.NestedMemoryTurnControls
