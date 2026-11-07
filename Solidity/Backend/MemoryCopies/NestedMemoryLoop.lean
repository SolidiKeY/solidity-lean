import Solidity.Backend.MemoryCopies.NestedMemoryRows

/-! Finite iteration composes the existing actual child turns. Children have
varying runtime lengths; earlier references weaken through later allocations. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem nested_memory_loop_more (primitive : PrimTy) (machine target : Machine) (source : Fin W) (parent total index : Fin W)
    (more : index.val < total.val)
    (body : run (nestedMemoryTurnCode primitive) (nestedMemoryControl machine source parent total index) = .ok target 0) :
    loopTurn (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive))
      (nestedMemoryControl machine source parent total index) = .inl target := by
  have condition : run Objects.childrenCondition (nestedMemoryControl machine source parent total index) =
      .ok ((nestedMemoryControl machine source parent total index).push w[1]) 0 := by
    simpa only [nestedMemoryControl, more, decide_true, bword] using
      Objects.childrenCondition_run (machine.push (.val source)) parent total index
  rw [loopTurn, condition]
  change (if (1 : Nat) = 0 then _ else _) = _
  rw [if_neg (by decide)]
  simp only [Machine.push]
  rw [body]

theorem nested_memory_loop_done (primitive : PrimTy) (machine : Machine) (source : Fin W) (parent total : Fin W) :
    loopTurn (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive))
      (nestedMemoryControl machine source parent total total) =
      .inr (.ok (nestedMemoryControl machine source parent total total) 0) := by
  have condition : run Objects.childrenCondition (nestedMemoryControl machine source parent total total) =
      .ok ((nestedMemoryControl machine source parent total total).push w[0]) 0 := by
    simpa only [nestedMemoryControl, Nat.lt_irrefl, decide_false, bword] using
      Objects.childrenCondition_run (machine.push (.val source)) parent total total
  rw [loopTurn, condition]
  rfl

theorem nested_memory_loop_run (primitive : PrimTy) {machine : Machine} {outcome : Evm.Out} {steps : Nat}
    (iteration : loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) steps machine = .inr outcome) :
    run (nestedMemoryLoopCode primitive) machine = outcome := by
  have loop : loopRun (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) machine = outcome :=
    loopRun_of_iterN iteration
  change (loopRun (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) machine).bind _ = outcome
  rw [loop]
  cases outcome <;> rfl

private theorem iteration_address {primitive : PrimTy} {steps : Nat} {machine target : Machine}
    {source source' parent total index : Fin W} (same : source = source')
    (iteration : loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) steps
      (nestedMemoryControl machine source parent total index) =
      .inr (.ok (nestedMemoryControl target source parent total total) 0)) :
    loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) steps
      (nestedMemoryControl machine source' parent total index) =
      .inr (.ok (nestedMemoryControl target source' parent total total) 0) := by
  cases same
  exact iteration

private theorem refusal_address {primitive : PrimTy} {steps : Nat} {machine : Machine}
    {source source' parent total index : Fin W} (same : source = source')
    (iteration : loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) steps
      (nestedMemoryControl machine source parent total index) = .inr .revert) :
    loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) steps
      (nestedMemoryControl machine source' parent total index) = .inr .revert := by
  cases same
  exact iteration

theorem nested_memory_loop_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + total.val ≤ cursor.val)
    (remaining : index.val + rows.length = total.val)
    (represented : NestedMemoryRowsRepr heap primitive source rows index.val)
    (fits : cursor.val + nestedStorageDemand rows < W) :
    NestedMemoryRowsLoopResult heap primitive rows source base frame cursor machine parent total index fits := by
  induction rows generalizing H heap source base cursor machine index with
  | nil =>
    have same : index = total := Fin.ext (by simpa only [List.length_nil, Nat.add_zero] using remaining)
    subst index
    have iteration : loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) (0 + 1)
        (nestedMemoryControl machine (base source.id) parent total total) =
        .inr (.ok (nestedMemoryControl machine (base source.id) parent total total) 0) := by
      rw [loopIterN, nested_memory_loop_done]
    unfold NestedMemoryRowsLoopResult
    simp only [nestedStorageValues, SVec.copyStToM_nil]
    refine ⟨base, machine, iteration, nested_memory_loop_run primitive iteration, ?_, BaseExtends.refl base,
      gap, ?_, rfl, (fun _ _ _ _ => rfl), (fun _ _ kept _ => kept), Heap.Keeps.refl heap, traversalFresh _ rfl heap, rfl⟩
    · simpa only [nestedStorageDemand, Nat.add_zero] using allocator
    · intro offset reference chosen
      cases chosen
  | cons row rows ih =>
    have more : index.val < total.val := by simp only [List.length_cons] at remaining; omega
    have nextBound : index.val + 1 < W := Nat.lt_of_le_of_lt (by omega) total.isLt
    have firstFits : cursor.val + (row.val.length + 1) < W := by
      simp only [nestedStorageDemand] at fits
      omega
    let index' : Fin W := ⟨index.val + 1, nextBound⟩
    let cursor' : Fin W := ⟨cursor.val + (row.val.length + 1), firstFits⟩
    let first := (primitiveArrayValue primitive row.val row.property).copyStToM heap rfl
    obtain ⟨child, selected, childLength, childSnapshot⟩ := represented 0 row rfl
    have selected' : heap.index source .dyn (indexValue index) = some child := by
      simpa only [Nat.add_zero, show wmod index.val = index from Fin.ext (Nat.mod_eq_of_lt index.isLt)] using selected
    obtain ⟨base1, machine1, body, allocated1, root, extension1, gap1, pointer, shape1, below1, gaps1, keeps1⟩ :=
      memory_row_turn_success heap primitive row source child base frame cursor machine parent total index
        allocator gap afterFrame beforeCursor more selected' childLength childSnapshot firstFits
    have nextIndex : wmod (index.val + 1) = index' := Fin.ext (Nat.mod_eq_of_lt nextBound)
    rw [nextIndex] at body
    have tailRepr : NestedMemoryRowsRepr first.heap primitive (source.wk first.ext) rows index'.val := by
      intro offset picked chosen
      have original : NestedMemoryRowsRepr first.heap primitive (source.wk first.ext) (row :: rows) index.val :=
        memory_rows_kept first.ext heap first.heap primitive source (row :: rows) index.val keeps1 represented
      simpa only [index', Nat.add_assoc, Nat.add_comm 1 offset] using original (offset + 1) picked chosen
    have tailFits : cursor'.val + nestedStorageDemand rows < W := by
      change cursor.val + (row.val.length + 1) + nestedStorageDemand rows < W
      simpa only [nestedStorageDemand, Nat.add_assoc] using fits
    have remaining' : index'.val + rows.length = total.val := by
      change index.val + 1 + rows.length = total.val
      simp only [List.length_cons] at remaining
      omega
    have beforeCursor' : parent.val + 1 + total.val ≤ cursor'.val := by
      change parent.val + 1 + total.val ≤ cursor.val + (row.val.length + 1)
      omega
    obtain ⟨base', target, tailIteration, tailRun, allocated, extension, finalGap, contents, shape, below, gaps, keeps, _, _⟩ :=
      ih first.heap base1 cursor' machine1 (source.wk first.ext) index' allocated1 gap1 beforeCursor' remaining' tailRepr tailFits
    let rest := (nestedStorageValues primitive rows).copyStToM first.heap rfl
    have iteration : loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) ((row :: rows).length + 1)
        (nestedMemoryControl machine (base source.id) parent total index) =
        .inr (.ok (nestedMemoryControl target (base source.id) parent total total) 0) := by
      rw [List.length_cons, loopIterN, nested_memory_loop_more primitive machine _ (base source.id) parent total index more body]
      exact iteration_address (extension1 source) tailIteration
    have cursorEq : cursor'.val + nestedStorageDemand rows = cursor.val + nestedStorageDemand (row :: rows) := by
      simp only [cursor', nestedStorageDemand, Nat.add_assoc]
    have allKeeps : Heap.Keeps ((nestedStorageValues primitive (row :: rows)).copyStToM heap rfl).ext heap
        ((nestedStorageValues primitive (row :: rows)).copyStToM heap rfl).heap :=
      SVec.keeps_copyStToM _ rfl heap
    simp only [nestedStorageValues, SVec.copyStToM_cons] at allKeeps
    unfold NestedMemoryRowsLoopResult
    simp only [nestedStorageValues, SVec.copyStToM_cons]
    refine ⟨base', target, iteration, nested_memory_loop_run primitive iteration, ?_,
      BaseExtends.trans first.ext extension1 extension, finalGap, ?_, ?_, ?_, ?_, allKeeps, traversalFresh _ rfl heap, ?_⟩
    · simpa only [cursorEq] using allocated
    · intro offset reference chosen
      cases offset with
      | zero =>
        change (HRef.wk rest.ext first.val :: rest.val.1)[0]? = some reference at chosen
        cases chosen
        have finalRoot : base' first.val.id = cursor := (extension first.val).trans root
        change target.mem (parent.val + 1 + index.val + 0) = .val (base' first.val.id)
        rw [Nat.add_zero, finalRoot, below _ (by omega) (by
          change parent.val + 1 + index.val < cursor.val + (row.val.length + 1)
          omega) (.inl (by change parent.val + 1 + index.val < parent.val + 1 + (index.val + 1); omega))]
        exact pointer
      | succ offset =>
        change (HRef.wk rest.ext first.val :: rest.val.1)[offset + 1]? = some reference at chosen
        change rest.val.1[offset]? = some reference at chosen
        have actual : target.mem (parent.val + 1 + index'.val + offset) = .val (base' reference.id) :=
          contents offset reference chosen
        simpa only [index', Nat.add_assoc, Nat.add_comm 1 offset] using actual
    · calc
        target = {machine1 with mem := target.mem} := shape
        _ = {machine with mem := target.mem} := by rw [shape1]
    · intro address positive lower outside
      rw [below address positive (by change address < cursor.val + (row.val.length + 1); omega) (by
        rcases outside with left | right
        · exact .inl (by change address < parent.val + 1 + (index.val + 1); omega)
        · exact .inr right)]
      exact below1 address positive lower (by rcases outside with left | right <;> omega)
    · intro lo hi oldGap upper
      exact gaps lo hi (gaps1 lo hi oldGap upper) (by change hi ≤ cursor.val + (row.val.length + 1); omega)

    · exact kept_snapshot (first.ext.trans rest.ext) heap rest.heap allKeeps
        (.ref (.array (.ref (.array (.prim primitive))))) source


theorem nested_memory_loop_abort (primitive : PrimTy) (machine : Machine) (source : Fin W) (parent total index : Fin W)
    (more : index.val < total.val)
    (body : run (nestedMemoryTurnCode primitive) (nestedMemoryControl machine source parent total index) = .revert) :
    loopTurn (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive))
      (nestedMemoryControl machine source parent total index) = .inr .revert := by
  have condition : run Objects.childrenCondition (nestedMemoryControl machine source parent total index) =
      .ok ((nestedMemoryControl machine source parent total index).push w[1]) 0 := by
    simpa only [nestedMemoryControl, more, decide_true, bword] using
      Objects.childrenCondition_run (machine.push (.val source)) parent total index
  rw [loopTurn, condition]
  change (if (1 : Nat) = 0 then _ else _) = _
  rw [if_neg (by decide)]
  simp only [Machine.push]
  rw [body]

theorem nested_memory_loop_refusal {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + total.val ≤ cursor.val)
    (remaining : index.val + rows.length = total.val)
    (represented : NestedMemoryRowsRepr heap primitive source rows index.val)
    (tooLarge : ¬ cursor.val + nestedStorageDemand rows < W) :
    loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) (rows.length + 1)
        (nestedMemoryControl machine (base source.id) parent total index) = .inr .revert ∧
      run (nestedMemoryLoopCode primitive) (nestedMemoryControl machine (base source.id) parent total index) = .revert := by
  induction rows generalizing H heap source base cursor machine index with
  | nil =>
    have room : cursor.val + nestedStorageDemand (primitive := primitive) [] < W := by
      simpa only [nestedStorageDemand, Nat.add_zero] using cursor.isLt
    exact (tooLarge room).elim
  | cons row rows ih =>
    have more : index.val < total.val := by simp only [List.length_cons] at remaining; omega
    obtain ⟨child, selected, childLength, childSnapshot⟩ := represented 0 row rfl
    have selected' : heap.index source .dyn (indexValue index) = some child := by
      simpa only [Nat.add_zero, show wmod index.val = index from Fin.ext (Nat.mod_eq_of_lt index.isLt)] using selected
    by_cases firstFits : cursor.val + (row.val.length + 1) < W
    · let first := (primitiveArrayValue primitive row.val row.property).copyStToM heap rfl
      obtain ⟨base1, machine1, body, allocated, root, extension, gap1, pointer, shape, below, gaps, keeps⟩ :=
        memory_row_turn_success heap primitive row source child base frame cursor machine parent total index
          allocator gap afterFrame beforeCursor more selected' childLength childSnapshot firstFits
      have indexBound : index.val + 1 < W := Nat.lt_of_le_of_lt (by omega) total.isLt
      let index' : Fin W := ⟨index.val + 1, indexBound⟩
      let cursor' : Fin W := ⟨cursor.val + (row.val.length + 1), firstFits⟩
      have nextIndex : wmod (index.val + 1) = index' := Fin.ext (Nat.mod_eq_of_lt indexBound)
      rw [nextIndex] at body
      have tailRepr : NestedMemoryRowsRepr first.heap primitive (source.wk first.ext) rows index'.val := by
        intro offset picked chosen
        have original : NestedMemoryRowsRepr first.heap primitive (source.wk first.ext) (row :: rows) index.val :=
          memory_rows_kept first.ext heap first.heap primitive source (row :: rows) index.val keeps represented
        simpa only [index', Nat.add_assoc, Nat.add_comm 1 offset] using original (offset + 1) picked chosen
      have tailTooLarge : ¬ cursor'.val + nestedStorageDemand rows < W := by
        change ¬ cursor.val + (row.val.length + 1) + nestedStorageDemand rows < W
        simpa only [nestedStorageDemand, Nat.add_assoc] using tooLarge
      obtain ⟨tailIteration, tailRun⟩ := ih first.heap base1 cursor' machine1 (source.wk first.ext) index' allocated gap1 (by
        change parent.val + 1 + total.val ≤ cursor.val + (row.val.length + 1)
        omega) (by
        change index.val + 1 + rows.length = total.val
        simp only [List.length_cons] at remaining
        omega) tailRepr tailTooLarge
      have iteration : loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) ((row :: rows).length + 1)
          (nestedMemoryControl machine (base source.id) parent total index) = .inr .revert := by
        rw [List.length_cons, loopIterN, nested_memory_loop_more primitive machine _ (base source.id) parent total index more body]
        exact refusal_address (extension source) tailIteration
      exact ⟨iteration, nested_memory_loop_run primitive iteration⟩
    · have refusal : run (nestedMemoryTurnCode primitive)
        (nestedMemoryControl machine (base source.id) parent total index) = .revert := memory_row_turn_refusal heap primitive row source child base frame cursor machine parent total index
        allocator selected' childLength firstFits
      have iteration : loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) ((row :: rows).length + 1)
          (nestedMemoryControl machine (base source.id) parent total index) = .inr .revert := by
        rw [List.length_cons, loopIterN, nested_memory_loop_abort primitive machine (base source.id) parent total index more refusal]
      exact ⟨iteration, nested_memory_loop_run primitive iteration⟩

theorem nested_memory_loop_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + total.val ≤ cursor.val)
    (remaining : index.val + rows.length = total.val)
    (represented : NestedMemoryRowsRepr heap primitive source rows index.val) :
    (∃ fits, NestedMemoryRowsLoopResult heap primitive rows source base frame cursor machine parent total index fits) ∨
    (¬ cursor.val + nestedStorageDemand rows < W ∧
      loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) (rows.length + 1)
        (nestedMemoryControl machine (base source.id) parent total index) = .inr .revert ∧
      run (nestedMemoryLoopCode primitive) (nestedMemoryControl machine (base source.id) parent total index) = .revert) := by
  by_cases fits : cursor.val + nestedStorageDemand rows < W
  · exact .inl ⟨fits, nested_memory_loop_success heap primitive rows base frame cursor machine source parent total index
      allocator gap afterFrame beforeCursor remaining represented fits⟩
  · exact .inr ⟨fits, nested_memory_loop_refusal heap primitive rows base frame cursor machine source parent total index
      allocator gap afterFrame beforeCursor remaining represented fits⟩

theorem nested_memory_loop_execute {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (parent : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + heap.len source .dyn))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + heap.len source .dyn ≤ cursor.val) :
    let rows := memoryChildRows heap primitive source
    let count := memoryChildCount heap primitive source
    (∃ fits, NestedMemoryRowsLoopResult heap primitive rows source base frame cursor machine parent count (wmod 0) fits) ∨
    (¬ cursor.val + nestedStorageDemand rows < W ∧
      loopIterN (run Objects.childrenCondition) (run (nestedMemoryTurnCode primitive)) (rows.length + 1)
        (nestedMemoryControl machine (base source.id) parent count (wmod 0)) = .inr .revert ∧
      run (nestedMemoryLoopCode primitive) (nestedMemoryControl machine (base source.id) parent count (wmod 0)) = .revert) := by
  exact nested_memory_loop_correct heap primitive (memoryChildRows heap primitive source) base frame cursor machine source
    parent (memoryChildCount heap primitive source) (wmod 0) allocator gap afterFrame beforeCursor
    (by simpa only [wmod_def, Nat.zero_mod, Nat.zero_add, memoryChildCount] using memory_rows_length heap primitive source)
    (memory_rows_repr heap primitive source)

def nestedMemoryLoop : NestedMemoryLoopCertificate := ⟨nested_memory_loop_execute⟩

#print axioms nested_memory_loop_more
#print axioms nested_memory_loop_done
#print axioms nested_memory_loop_run
#print axioms nested_memory_loop_success
#print axioms nested_memory_loop_abort
#print axioms nested_memory_loop_refusal
#print axioms nested_memory_loop_correct
#print axioms nested_memory_loop_execute
#print axioms nestedMemoryLoop
end Solidity.Backend.MemoryCopies
