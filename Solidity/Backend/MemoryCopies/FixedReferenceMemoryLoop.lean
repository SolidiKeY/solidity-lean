import Solidity.Backend.MemoryCopies.FixedReferenceMemoryRows

/-! Finite headerless fixed-parent traversal composes actual checked child steps.
Repeated input edges are copied freshly and old source snapshots survive. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem fixed_reference_memory_loop_more (primitive : PrimTy) (size : Nat) (machine target : Machine) (source : Fin W) (parent total index : Fin W)
    (more : index.val < total.val)
    (body : run (fixedReferenceMemoryTurnCode primitive size) (nestedMemoryControl machine source parent total index) = .ok target 0) :
    loopTurn (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size))
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

theorem fixed_reference_memory_loop_done (primitive : PrimTy) (size : Nat) (machine : Machine) (source : Fin W) (parent total : Fin W) :
    loopTurn (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size))
      (nestedMemoryControl machine source parent total total) =
      .inr (.ok (nestedMemoryControl machine source parent total total) 0) := by
  have condition : run Objects.childrenCondition (nestedMemoryControl machine source parent total total) =
      .ok ((nestedMemoryControl machine source parent total total).push w[0]) 0 := by
    simpa only [nestedMemoryControl, Nat.lt_irrefl, decide_false, bword] using
      Objects.childrenCondition_run (machine.push (.val source)) parent total total
  rw [loopTurn, condition]
  rfl

theorem fixed_reference_memory_loop_run (primitive : PrimTy) (size : Nat) {machine : Machine} {outcome : Evm.Out} {steps : Nat}
    (iteration : loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) steps machine = .inr outcome) :
    run (fixedReferenceMemoryLoopCode primitive size) machine = outcome := by
  have loop : loopRun (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) machine = outcome :=
    loopRun_of_iterN iteration
  change (loopRun (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) machine).bind _ = outcome
  rw [loop]
  cases outcome <;> rfl

private theorem iteration_address {primitive : PrimTy} {size : Nat} {steps : Nat} {machine target : Machine}
    {source source' parent total index : Fin W} (same : source = source')
    (iteration : loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) steps
      (nestedMemoryControl machine source parent total index) =
      .inr (.ok (nestedMemoryControl target source parent total total) 0)) :
    loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) steps
      (nestedMemoryControl machine source' parent total index) =
      .inr (.ok (nestedMemoryControl target source' parent total total) 0) := by
  cases same
  exact iteration

private theorem refusal_address {primitive : PrimTy} {size : Nat} {steps : Nat} {machine : Machine}
    {source source' parent total index : Fin W} (same : source = source')
    (iteration : loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) steps
      (nestedMemoryControl machine source parent total index) = .inr .revert) :
    loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) steps
      (nestedMemoryControl machine source' parent total index) = .inr .revert := by
  cases same
  exact iteration

theorem fixed_reference_memory_loop_success {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size)) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + max 1 total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + max 1 total.val ≤ cursor.val)
    (remaining : index.val + rows.length = total.val)
    (represented : FixedReferenceMemoryRowsRepr heap primitive size source rows index.val)
    (fits : cursor.val + nestedStorageDemand rows < W) :
    FixedReferenceMemoryRowsLoopResult heap primitive size rows source base frame cursor machine parent total index fits := by
  have parentPositive : 0 < parent.val := Nat.lt_of_lt_of_le allocator.free.reserved afterFrame
  induction rows generalizing H heap source base cursor machine index with
  | nil =>
    have same : index = total := Fin.ext (by simpa only [List.length_nil, Nat.add_zero] using remaining)
    subst index
    have iteration : loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) (0 + 1)
        (nestedMemoryControl machine (base source.id) parent total total) =
        .inr (.ok (nestedMemoryControl machine (base source.id) parent total total) 0) := by
      rw [loopIterN, fixed_reference_memory_loop_done]
    unfold FixedReferenceMemoryRowsLoopResult
    simp only [nestedStorageValues, SVec.copyStToM_nil]
    refine ⟨base, machine, iteration, fixed_reference_memory_loop_run primitive size iteration, ?_, BaseExtends.refl base,
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
    have selected' : heap.index source .fixed (indexValue index) = some child := by
      simpa only [Nat.add_zero, show wmod index.val = index from Fin.ext (Nat.mod_eq_of_lt index.isLt)] using selected
    obtain ⟨base1, machine1, body, allocated1, root, extension1, gap1, pointer, shape1, below1, gaps1, keeps1⟩ :=
      fixed_memory_row_turn_success heap primitive size row source child base frame cursor machine parent total index
        allocator gap afterFrame beforeCursor more selected' childLength childSnapshot firstFits
    have nextIndex : wmod (index.val + 1) = index' := Fin.ext (Nat.mod_eq_of_lt nextBound)
    rw [nextIndex] at body
    have tailRepr : FixedReferenceMemoryRowsRepr first.heap primitive size (source.wk first.ext) rows index'.val := by
      intro offset picked chosen
      have original : FixedReferenceMemoryRowsRepr first.heap primitive size (source.wk first.ext) (row :: rows) index.val :=
        fixed_memory_rows_kept first.ext heap first.heap primitive size source (row :: rows) index.val keeps1 represented
      simpa only [index', Nat.add_assoc, Nat.add_comm 1 offset] using original (offset + 1) picked chosen
    have tailFits : cursor'.val + nestedStorageDemand rows < W := by
      change cursor.val + (row.val.length + 1) + nestedStorageDemand rows < W
      simpa only [nestedStorageDemand, Nat.add_assoc] using fits
    have remaining' : index'.val + rows.length = total.val := by
      change index.val + 1 + rows.length = total.val
      simp only [List.length_cons] at remaining
      omega
    have beforeCursor' : parent.val + max 1 total.val ≤ cursor'.val := by
      change parent.val + max 1 total.val ≤ cursor.val + (row.val.length + 1)
      omega
    obtain ⟨base', target, tailIteration, tailRun, allocated, extension, finalGap, contents, shape, below, gaps, keeps, _, _⟩ :=
      ih first.heap base1 cursor' machine1 (source.wk first.ext) index' allocated1 gap1 beforeCursor' remaining' tailRepr tailFits
    let rest := (nestedStorageValues primitive rows).copyStToM first.heap rfl
    have iteration : loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) ((row :: rows).length + 1)
        (nestedMemoryControl machine (base source.id) parent total index) =
        .inr (.ok (nestedMemoryControl target (base source.id) parent total total) 0) := by
      rw [List.length_cons, loopIterN, fixed_reference_memory_loop_more primitive size machine _ (base source.id) parent total index more body]
      exact iteration_address (extension1 source) tailIteration
    have cursorEq : cursor'.val + nestedStorageDemand rows = cursor.val + nestedStorageDemand (row :: rows) := by
      simp only [cursor', nestedStorageDemand, Nat.add_assoc]
    have allKeeps : Heap.Keeps ((nestedStorageValues primitive (row :: rows)).copyStToM heap rfl).ext heap
        ((nestedStorageValues primitive (row :: rows)).copyStToM heap rfl).heap :=
      SVec.keeps_copyStToM _ rfl heap
    simp only [nestedStorageValues, SVec.copyStToM_cons] at allKeeps
    unfold FixedReferenceMemoryRowsLoopResult
    simp only [nestedStorageValues, SVec.copyStToM_cons]
    refine ⟨base', target, iteration, fixed_reference_memory_loop_run primitive size iteration, ?_,
      BaseExtends.trans first.ext extension1 extension, finalGap, ?_, ?_, ?_, ?_, allKeeps, traversalFresh _ rfl heap, ?_⟩
    · simpa only [cursorEq] using allocated
    · intro offset reference chosen
      cases offset with
      | zero =>
        change (HRef.wk rest.ext first.val :: rest.val.1)[0]? = some reference at chosen
        cases chosen
        have finalRoot : base' first.val.id = cursor := (extension first.val).trans root
        change target.mem (parent.val + index.val + 0) = .val (base' first.val.id)
        rw [Nat.add_zero, finalRoot, below _ (by omega) (by
          change parent.val + index.val < cursor.val + (row.val.length + 1)
          omega) (.inl (by change parent.val + index.val < parent.val + (index.val + 1); omega))]
        exact pointer
      | succ offset =>
        change (HRef.wk rest.ext first.val :: rest.val.1)[offset + 1]? = some reference at chosen
        change rest.val.1[offset]? = some reference at chosen
        have actual : target.mem (parent.val + index'.val + offset) = .val (base' reference.id) :=
          contents offset reference chosen
        simpa only [index', Nat.add_assoc, Nat.add_comm 1 offset] using actual
    · calc
        target = {machine1 with mem := target.mem} := shape
        _ = {machine with mem := target.mem} := by rw [shape1]
    · intro address positive lower outside
      rw [below address positive (by change address < cursor.val + (row.val.length + 1); omega) (by
        rcases outside with left | right
        · exact .inl (by change address < parent.val + (index.val + 1); omega)
        · exact .inr right)]
      exact below1 address positive lower (by rcases outside with left | right <;> omega)
    · intro lo hi oldGap upper
      exact gaps lo hi (gaps1 lo hi oldGap upper) (by change hi ≤ cursor.val + (row.val.length + 1); omega)

    · exact kept_snapshot (first.ext.trans rest.ext) heap rest.heap allKeeps
        (.ref (.fixed (.ref (.array (.prim primitive))) size)) source


theorem fixed_reference_memory_loop_abort (primitive : PrimTy) (size : Nat) (machine : Machine) (source : Fin W) (parent total index : Fin W)
    (more : index.val < total.val)
    (body : run (fixedReferenceMemoryTurnCode primitive size) (nestedMemoryControl machine source parent total index) = .revert) :
    loopTurn (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size))
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

theorem fixed_reference_memory_loop_refusal {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size)) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + max 1 total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + max 1 total.val ≤ cursor.val)
    (remaining : index.val + rows.length = total.val)
    (represented : FixedReferenceMemoryRowsRepr heap primitive size source rows index.val)
    (tooLarge : ¬ cursor.val + nestedStorageDemand rows < W) :
    loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) (rows.length + 1)
        (nestedMemoryControl machine (base source.id) parent total index) = .inr .revert ∧
      run (fixedReferenceMemoryLoopCode primitive size) (nestedMemoryControl machine (base source.id) parent total index) = .revert := by
  induction rows generalizing H heap source base cursor machine index with
  | nil =>
    have room : cursor.val + nestedStorageDemand (primitive := primitive) [] < W := by
      simpa only [nestedStorageDemand, Nat.add_zero] using cursor.isLt
    exact (tooLarge room).elim
  | cons row rows ih =>
    have more : index.val < total.val := by simp only [List.length_cons] at remaining; omega
    obtain ⟨child, selected, childLength, childSnapshot⟩ := represented 0 row rfl
    have selected' : heap.index source .fixed (indexValue index) = some child := by
      simpa only [Nat.add_zero, show wmod index.val = index from Fin.ext (Nat.mod_eq_of_lt index.isLt)] using selected
    by_cases firstFits : cursor.val + (row.val.length + 1) < W
    · let first := (primitiveArrayValue primitive row.val row.property).copyStToM heap rfl
      obtain ⟨base1, machine1, body, allocated, root, extension, gap1, pointer, shape, below, gaps, keeps⟩ :=
        fixed_memory_row_turn_success heap primitive size row source child base frame cursor machine parent total index
          allocator gap afterFrame beforeCursor more selected' childLength childSnapshot firstFits
      have indexBound : index.val + 1 < W := Nat.lt_of_le_of_lt (by omega) total.isLt
      let index' : Fin W := ⟨index.val + 1, indexBound⟩
      let cursor' : Fin W := ⟨cursor.val + (row.val.length + 1), firstFits⟩
      have nextIndex : wmod (index.val + 1) = index' := Fin.ext (Nat.mod_eq_of_lt indexBound)
      rw [nextIndex] at body
      have tailRepr : FixedReferenceMemoryRowsRepr first.heap primitive size (source.wk first.ext) rows index'.val := by
        intro offset picked chosen
        have original : FixedReferenceMemoryRowsRepr first.heap primitive size (source.wk first.ext) (row :: rows) index.val :=
          fixed_memory_rows_kept first.ext heap first.heap primitive size source (row :: rows) index.val keeps represented
        simpa only [index', Nat.add_assoc, Nat.add_comm 1 offset] using original (offset + 1) picked chosen
      have tailTooLarge : ¬ cursor'.val + nestedStorageDemand rows < W := by
        change ¬ cursor.val + (row.val.length + 1) + nestedStorageDemand rows < W
        simpa only [nestedStorageDemand, Nat.add_assoc] using tooLarge
      obtain ⟨tailIteration, tailRun⟩ := ih first.heap base1 cursor' machine1 (source.wk first.ext) index' allocated gap1 (by
        change parent.val + max 1 total.val ≤ cursor.val + (row.val.length + 1)
        omega) (by
        change index.val + 1 + rows.length = total.val
        simp only [List.length_cons] at remaining
        omega) tailRepr tailTooLarge
      have iteration : loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) ((row :: rows).length + 1)
          (nestedMemoryControl machine (base source.id) parent total index) = .inr .revert := by
        rw [List.length_cons, loopIterN, fixed_reference_memory_loop_more primitive size machine _ (base source.id) parent total index more body]
        exact refusal_address (extension source) tailIteration
      exact ⟨iteration, fixed_reference_memory_loop_run primitive size iteration⟩
    · have refusal : run (fixedReferenceMemoryTurnCode primitive size)
        (nestedMemoryControl machine (base source.id) parent total index) = .revert := fixed_memory_row_turn_refusal heap primitive size row source child base frame cursor machine parent total index
        allocator selected' childLength firstFits
      have iteration : loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) ((row :: rows).length + 1)
          (nestedMemoryControl machine (base source.id) parent total index) = .inr .revert := by
        rw [List.length_cons, loopIterN, fixed_reference_memory_loop_abort primitive size machine (base source.id) parent total index more refusal]
      exact ⟨iteration, fixed_reference_memory_loop_run primitive size iteration⟩

theorem fixed_reference_memory_loop_correct {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size)) (parent total index : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + max 1 total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + max 1 total.val ≤ cursor.val)
    (remaining : index.val + rows.length = total.val)
    (represented : FixedReferenceMemoryRowsRepr heap primitive size source rows index.val) :
    (∃ fits, FixedReferenceMemoryRowsLoopResult heap primitive size rows source base frame cursor machine parent total index fits) ∨
    (¬ cursor.val + nestedStorageDemand rows < W ∧
      loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) (rows.length + 1)
        (nestedMemoryControl machine (base source.id) parent total index) = .inr .revert ∧
      run (fixedReferenceMemoryLoopCode primitive size) (nestedMemoryControl machine (base source.id) parent total index) = .revert) := by
  by_cases fits : cursor.val + nestedStorageDemand rows < W
  · exact .inl ⟨fits, fixed_reference_memory_loop_success heap primitive size rows base frame cursor machine source parent total index
      allocator gap afterFrame beforeCursor remaining represented fits⟩
  · exact .inr ⟨fits, fixed_reference_memory_loop_refusal heap primitive size rows base frame cursor machine source parent total index
      allocator gap afterFrame beforeCursor remaining represented fits⟩

theorem fixed_reference_memory_loop_execute {H : HTy} (heap : Heap H) (primitive : PrimTy) (size : Nat)
    (source : HRef H (.fixed (.ref (.array (.prim primitive))) size)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (parent : Fin W)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + max 1 size))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + max 1 size ≤ cursor.val) :
    let rows := fixedMemoryChildRows heap primitive size source
    let count := wmod size
    (∃ fits, FixedReferenceMemoryRowsLoopResult heap primitive size rows source base frame cursor machine parent count (wmod 0) fits) ∨
    (¬ cursor.val + nestedStorageDemand rows < W ∧
      loopIterN (run Objects.childrenCondition) (run (fixedReferenceMemoryTurnCode primitive size)) (rows.length + 1)
        (nestedMemoryControl machine (base source.id) parent count (wmod 0)) = .inr .revert ∧
      run (fixedReferenceMemoryLoopCode primitive size) (nestedMemoryControl machine (base source.id) parent count (wmod 0)) = .revert) := by
  have sizeBound : size < W := by have cursorBound : cursor.val < W := cursor.isLt; omega
  have countValue : (wmod size).val = size := Nat.mod_eq_of_lt sizeBound
  have remaining : (wmod 0).val + (fixedMemoryChildRows heap primitive size source).length = (wmod size).val := by
    rw [fixed_memory_rows_length,fixed_memory_length,countValue]
    simp only [wmod_def,Nat.zero_mod,Nat.zero_add]
  exact fixed_reference_memory_loop_correct heap primitive size (fixedMemoryChildRows heap primitive size source)
    base frame cursor machine source parent (wmod size) (wmod 0) allocator
    (by rw [countValue]; exact gap) afterFrame (by simpa only [countValue] using beforeCursor)
    remaining (fixed_memory_rows_repr heap primitive size source sizeBound)

def fixedReferenceMemoryLoop : FixedReferenceMemoryLoopCertificate := ⟨fixed_reference_memory_loop_execute⟩

/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_memory_loop_more' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_memory_loop_more
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_memory_loop_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_memory_loop_done
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_memory_loop_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_memory_loop_run
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_memory_loop_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_memory_loop_success
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_memory_loop_abort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_memory_loop_abort
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_memory_loop_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_memory_loop_refusal
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_memory_loop_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_memory_loop_correct
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_memory_loop_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_memory_loop_execute
/--
info: 'Solidity.Backend.MemoryCopies.fixedReferenceMemoryLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixedReferenceMemoryLoop

end Solidity.Backend.MemoryCopies
