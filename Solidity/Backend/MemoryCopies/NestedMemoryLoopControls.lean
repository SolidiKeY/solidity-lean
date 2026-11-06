import Solidity.Backend.MemoryCopies.NestedMemoryLoop
import Solidity.Backend.MemoryCopies.StorageMemoryPipeline

/-! A real dynamic parent contains two aliases of the same variable-length
child. A separate reservation receives the new deep-copy pointer. -/
namespace Solidity.Backend.MemoryCopies.NestedMemoryLoopControls
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

private def row (payloads : List (Fin W)) (bounded : payloads.length < 128) : PrimitiveStorageRow .uint :=
  ⟨values payloads, by rw [values, List.length_map]; exact Nat.lt_trans bounded wide⟩
private def children (payloads : List (Fin W)) (bounded : payloads.length < 128) :=
  [row payloads bounded, row payloads bounded]
private theorem source_rows (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    memoryChildRows (heap payloads bounded) .uint source = children payloads bounded := by
  with_unfolding_all rfl
private theorem source_gap (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.Gap (heap payloads bounded) base 192 195 := by
  intro Q reference
  rcases (reservation payloads bounded).2 reference with left | right
  · exact .inl left
  · exact .inr (by omega)

theorem certificate_inhabited : NestedMemoryLoopCertificate := nestedMemoryLoop

theorem actual_typed (payloads : List (Fin W)) (bounded : payloads.length < 128) : ∃ fits,
    NestedMemoryRowsLoopResult (heap payloads bounded) .uint (children payloads bounded) source base 8 (wmod 196)
      (reserved payloads) (wmod 192) (wmod 2) (wmod 0) fits := by
  have cost : nestedStorageDemand (children payloads bounded) = 2 * (payloads.length + 1) := by
    simp only [children, nestedStorageDemand, row, values, List.length_map]
    omega
  have fits : (wmod 196).val + nestedStorageDemand (children payloads bounded) < W := by
    rw [cost]
    change 196 + 2 * (payloads.length + 1) < W
    have large : 1024 < W := by decide
    omega
  have represented : NestedMemoryRowsRepr (heap payloads bounded) .uint source (children payloads bounded) 0 := by
    rw [← source_rows]
    exact memory_rows_repr _ _ _
  exact ⟨fits, nested_memory_loop_success _ .uint _ base 8 (wmod 196) (reserved payloads) source
    (wmod 192) (wmod 2) (wmod 0) (reservation payloads bounded).1 (source_gap payloads bounded)
    (by decide) (by decide) (by with_unfolding_all rfl) represented fits⟩

theorem actual_runtime (payloads : List (Fin W)) (bounded : payloads.length < 128) : ∃ target : Machine,
    run (nestedMemoryLoopCode .uint) (nestedMemoryControl (reserved payloads) (wmod 160) (wmod 192) (wmod 2) (wmod 0)) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 2) (wmod 2)) 0 ∧
    target.mem 0 = .val (wmod (196 + 2 * (payloads.length + 1))) ∧
    target.mem 161 = w[16] ∧ target.mem 162 = w[16] ∧ target.mem 192 = w[3] ∧
    target.mem 195 = w[0] ∧ target.stack = [w[77]] ∧
    (∀ index payload, payloads[index]? = some payload → target.mem (17 + index) = .val payload) := by
  obtain ⟨fits, base', target, iteration, ran, allocated, extension, gap, contents, shape, below, gaps, keeps, fresh, retained⟩ :=
    actual_typed payloads bounded
  have cost : nestedStorageDemand (children payloads bounded) = 2 * (payloads.length + 1) := by
    simp only [children, nestedStorageDemand, row, values, List.length_map]
    omega
  refine ⟨target, ran, ?_, ?_, ?_, ?_, ?_, congrArg Machine.stack shape, ?_⟩
  · refine allocated.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    change 196 + nestedStorageDemand (children payloads bounded) = (196 + 2 * (payloads.length + 1)) % W
    rw [← cost]
    exact (Nat.mod_eq_of_lt fits).symm
  · exact (below 161 (by decide) (by decide) (.inl (by decide))).trans
      ((allocateMachine_other _ _ _ _ (by decide) (by decide)).trans rfl)
  · exact (below 162 (by decide) (by decide) (.inl (by decide))).trans
      ((allocateMachine_other _ _ _ _ (by decide) (by decide)).trans rfl)
  · exact (below 192 (by decide) (by decide) (.inl (by decide))).trans (allocateMachine_header _ _ _ (by decide))
  · exact (below 195 (by decide) (by decide) (.inr (by decide))).trans
      ((allocateMachine_other _ _ _ _ (by decide) (by decide)).trans (by
        simp only [machine, if_neg (by decide : 195 ≠ 0), if_neg (by decide : 195 ≠ 7),
          if_neg (by decide : 195 ≠ 16), if_neg (by decide : 195 ≠ 160),
          if_neg (by decide : ¬(195 = 161 ∨ 195 = 162)), if_neg (show ¬(17 ≤ 195 ∧ 195 < 17 + payloads.length) by omega)]))
  · intro index payload chosen
    have lower : index < payloads.length := lt_of_getElem? chosen
    rw [below (17 + index) (by omega) (by change 17 + index < 196; omega)
      (.inl (by change 17 + index < 193; omega))]
    change (allocateMachine (machine payloads) (wmod 192) (wmod 3)).mem (17 + index) = _
    rw [allocateMachine_other _ _ _ _ (by change 17 + index ≠ 192; omega) (by omega)]
    simp only [machine, if_neg (show 17 + index ≠ 0 by omega), if_neg (show 17 + index ≠ 7 by omega),
      if_neg (show 17 + index ≠ 16 by omega), if_neg (show 17 + index ≠ 160 by omega),
      if_neg (show ¬(17 + index = 161 ∨ 17 + index = 162) by omega),
      if_pos (show 17 ≤ 17 + index ∧ 17 + index < 17 + payloads.length by omega), Nat.add_sub_cancel_left, chosen, Option.getD_some]

theorem empty_children_runtime : ∃ target : Machine,
    run (nestedMemoryLoopCode .uint) (nestedMemoryControl (reserved []) (wmod 160) (wmod 192) (wmod 2) (wmod 0)) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 2) (wmod 2)) 0 ∧ target.mem 0 = w[198] := by
  obtain ⟨target, ran, cursor, _⟩ := actual_runtime [] (by decide)
  exact ⟨target, ran, cursor⟩

theorem pair_runtime : ∃ target : Machine,
    run (nestedMemoryLoopCode .uint) (nestedMemoryControl (reserved [wmod 11,wmod 23]) (wmod 160) (wmod 192) (wmod 2) (wmod 0)) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 2) (wmod 2)) 0 ∧
    target.mem 0 = w[202] ∧ target.mem 17 = w[11] ∧ target.mem 18 = w[23] := by
  obtain ⟨target, ran, cursor, _, _, _, _, _, words⟩ := actual_runtime [wmod 11,wmod 23] (by decide)
  exact ⟨target, ran, cursor, words 0 (wmod 11) rfl, words 1 (wmod 23) rfl⟩

private def long : List (Fin W) := List.ofFn (fun i : Fin 64 => wmod (i.val + 1))
theorem long_runtime : ∃ target : Machine,
    run (nestedMemoryLoopCode .uint) (nestedMemoryControl (reserved long) (wmod 160) (wmod 192) (wmod 2) (wmod 0)) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 2) (wmod 2)) 0 ∧
    target.mem 0 = w[326] ∧ target.mem 17 = w[1] ∧ target.mem 80 = w[64] := by
  obtain ⟨target, ran, cursor, _, _, _, _, _, words⟩ := actual_runtime long (by rw [long, List.length_ofFn]; decide)
  exact ⟨target, ran, by simpa only [long, List.length_ofFn] using cursor,
    words 0 (wmod 1) (by decide +kernel), words 63 (wmod 64) (by decide +kernel)⟩

theorem wrong_single_child_cursor (target : Machine)
    (ran : run (nestedMemoryLoopCode .uint) (nestedMemoryControl (reserved [wmod 11,wmod 23]) (wmod 160) (wmod 192) (wmod 2) (wmod 0)) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 2) (wmod 2)) 0) : target.mem 0 ≠ w[199] := by
  obtain ⟨actual, execution, cursor, _⟩ := pair_runtime
  rw [ran] at execution
  have same : target.mem 0 = actual.mem 0 := congrArg (fun machine => machine.mem 0) (Out.ok.inj execution).1
  rw [same, cursor]
  decide

theorem aliased_source_fresh_pointers (payloads : List (Fin W)) (bounded : payloads.length < 128) : ∃ target : Machine,
    run (nestedMemoryLoopCode .uint) (nestedMemoryControl (reserved payloads) (wmod 160) (wmod 192) (wmod 2) (wmod 0)) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 2) (wmod 2)) 0 ∧ target.mem 193 ≠ target.mem 194 := by
  obtain ⟨fits, base', target, _, ran, allocated, _, _, contents, _, _, _, _, _, _⟩ := actual_typed payloads bounded
  let value := primitiveArrayValue .uint (row payloads bounded).val (row payloads bounded).property
  let first := value.copyStToM (heap payloads bounded) rfl
  let second := value.copyStToM first.heap rfl
  let left : HRef second.H' R := HRef.wk second.ext first.val
  simp only [children, nestedStorageValues, SVec.copyStToM_cons, SVec.copyStToM_nil] at allocated contents
  have pickedLeft : [left, second.val][0]? = some left := rfl
  have pickedRight : [left, second.val][1]? = some second.val := rfl
  have firstBound : first.val.id < first.H'.length := first.val.id_lt
  have secondBound : first.H'.length ≤ second.val.id := SVal.copyStToM_id_ge first.heap value rfl
  have different : left.id ≠ second.val.id := Nat.ne_of_lt (Nat.lt_of_lt_of_le firstBound secondBound)
  have separated : (base' left.id).val + Objects.cells second.heap left ≤ (base' second.val.id).val ∨
      (base' second.val.id).val + Objects.cells second.heap second.val ≤ (base' left.id).val :=
    allocated.heap.owner.separated left second.val different
  have positiveLeft : 0 < Objects.cells second.heap left := Objects.cells_pos second.heap left
  have positiveRight : 0 < Objects.cells second.heap second.val := Objects.cells_pos second.heap second.val
  have rootDifferent : base' left.id ≠ base' second.val.id := by
    intro equal
    have same : (base' left.id).val = (base' second.val.id).val := congrArg Fin.val equal
    rcases separated with before | after <;> omega
  refine ⟨target, ran, ?_⟩
  have leftPointer : target.mem 193 = .val (base' left.id) := contents 0 left pickedLeft
  have rightPointer : target.mem 194 = .val (base' second.val.id) := contents 1 second.val pickedRight
  rw [leftPointer, rightPointer]
  exact fun equal => rootDifferent (Word.val.inj equal)

private def moved (payloads : List (Fin W)) (cursor : Fin W) : Machine := writeMachine (reserved payloads) 0 (.val cursor)
private theorem moved_allocator (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (cursor : Fin W) (above : 196 ≤ cursor.val) : Objects.AllocatorRepr (heap payloads bounded) base 8 cursor (moved payloads cursor) := by
  have old : Objects.AllocatorRepr (heap payloads bounded) base 8 (wmod 196) (reserved payloads) := (reservation payloads bounded).1
  refine ⟨old.heap.localWrite 0 (by decide) (.val cursor), ⟨by decide, by omega, rfl, ?_⟩, ?_⟩
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (old.free.zero address (by change 196 ≤ address; omega))
  · intro Q reference
    have live : (base reference.id).val + Objects.cells (heap payloads bounded) reference ≤ 196 := old.live reference
    omega

private def late : Fin W := ⟨W - 4, by
  have large : 1024 < W := by decide
  omega⟩
theorem late_refusal_after_successful_child : ∃ middle : Machine,
    run (nestedMemoryTurnCode .uint)
      (nestedMemoryControl (moved [wmod 11,wmod 23] late) (wmod 160) (wmod 192) (wmod 2) (wmod 0)) =
      .ok (nestedMemoryControl middle (wmod 160) (wmod 192) (wmod 2) (wmod 1)) 0 ∧
    run (nestedMemoryLoopCode .uint)
      (nestedMemoryControl (moved [wmod 11,wmod 23] late) (wmod 160) (wmod 192) (wmod 2) (wmod 0)) = .revert := by
  have large : 1024 < W := by decide
  have represented : NestedMemoryRowsRepr (heap [wmod 11,wmod 23] (by decide)) .uint source
      (children [wmod 11,wmod 23] (by decide)) 0 := by
    rw [← source_rows]
    exact memory_rows_repr _ _ _
  have allocated : Objects.AllocatorRepr (heap [wmod 11,wmod 23] (by decide)) base 8 late (moved [wmod 11,wmod 23] late) := moved_allocator [wmod 11,wmod 23] (by decide) late (by change 196 ≤ W - 4; omega)
  have firstFits : late.val + ((row [wmod 11,wmod 23] (by decide)).val.length + 1) < W := by
    change W - 4 + (2 + 1) < W
    omega
  obtain ⟨_, middle, body, _⟩ := memory_row_turn_success _ .uint (row [wmod 11,wmod 23] (by decide)) source child base 8 late
    (moved [wmod 11,wmod 23] late) (wmod 192) (wmod 2) (wmod 0) allocated
    (source_gap _ (by decide)) (by decide) (by change 195 ≤ W - 4; omega) (by decide)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by rw [primitiveArray_snapshot]; with_unfolding_all rfl) firstFits
  refine ⟨middle, body, ?_⟩
  exact (nested_memory_loop_refusal _ .uint (children [wmod 11,wmod 23] (by decide)) base 8 late
    (moved [wmod 11,wmod 23] late) source (wmod 192) (wmod 2) (wmod 0) allocated
    (source_gap _ (by decide)) (by decide) (by change 195 ≤ W - 4; omega) (by with_unfolding_all rfl)
    represented (by change ¬ W - 4 + 6 < W; omega)).2

theorem saturated_completed_suffix : ∃ target : Machine,
    run (nestedMemoryLoopCode .uint) (nestedMemoryControl (moved [] wMax) (wmod 160) (wmod 192) (wmod 2) (wmod 2)) =
      .ok (nestedMemoryControl target (wmod 160) (wmod 192) (wmod 2) (wmod 2)) 0 ∧ target = moved [] wMax := by
  have iteration : loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode .uint)) 1
      (nestedMemoryControl (moved [] wMax) (wmod 160) (wmod 192) (wmod 2) (wmod 2)) =
      .inr (.ok (nestedMemoryControl (moved [] wMax) (wmod 160) (wmod 192) (wmod 2) (wmod 2)) 0) := by
    rw [loopIterN, nested_memory_loop_done]
  exact ⟨_, nested_memory_loop_run .uint iteration, rfl⟩

#print axioms certificate_inhabited
#print axioms actual_typed
#print axioms actual_runtime
#print axioms empty_children_runtime
#print axioms pair_runtime
#print axioms long_runtime
#print axioms wrong_single_child_cursor
#print axioms aliased_source_fresh_pointers
#print axioms late_refusal_after_successful_child
#print axioms saturated_completed_suffix
end Solidity.Backend.MemoryCopies.NestedMemoryLoopControls
