import Solidity.Backend.MemoryCopies.NestedStorageLoopInterface

/-! Finite iteration composes the existing actual child turns. Children have
varying runtime lengths; earlier references weaken through later allocations. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem nested_storage_loop_more (machine target : Machine) (source : Slot) (parent total index : Fin W)
    (more : index.val < total.val)
    (body : run nestedStorageTurnCode (nestedStorageControl machine source parent total index) = .ok target 0) :
    loopTurn (run Objects.childrenCondition) (run nestedStorageTurnCode)
      (nestedStorageControl machine source parent total index) = .inl target := by
  have condition : run Objects.childrenCondition (nestedStorageControl machine source parent total index) =
      .ok ((nestedStorageControl machine source parent total index).push w[1]) 0 := by
    simpa only [nestedStorageControl, more, decide_true, bword] using
      Objects.childrenCondition_run (machine.push (.slot source)) parent total index
  rw [loopTurn, condition]
  change (if (1 : Nat) = 0 then _ else _) = _
  rw [if_neg (by decide)]
  simp only [Machine.push]
  rw [body]

theorem nested_storage_loop_done (machine : Machine) (source : Slot) (parent total : Fin W) :
    loopTurn (run Objects.childrenCondition) (run nestedStorageTurnCode)
      (nestedStorageControl machine source parent total total) =
      .inr (.ok (nestedStorageControl machine source parent total total) 0) := by
  have condition : run Objects.childrenCondition (nestedStorageControl machine source parent total total) =
      .ok ((nestedStorageControl machine source parent total total).push w[0]) 0 := by
    simpa only [nestedStorageControl, Nat.lt_irrefl, decide_false, bword] using
      Objects.childrenCondition_run (machine.push (.slot source)) parent total total
  rw [loopTurn, condition]
  rfl

theorem nested_storage_loop_run {machine : Machine} {outcome : Evm.Out} {steps : Nat}
    (iteration : loopIterN (run Objects.childrenCondition) (run nestedStorageTurnCode) steps machine = .inr outcome) :
    run nestedStorageLoopCode machine = outcome := by
  have loop : loopRun (run Objects.childrenCondition) (run nestedStorageTurnCode) machine = outcome :=
    loopRun_of_iterN iteration
  change (loopRun (run Objects.childrenCondition) (run nestedStorageTurnCode) machine).bind _ = outcome
  rw [loop]
  cases outcome <;> rfl

theorem nested_storage_loop_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (parent total index : Fin W) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + total.val ≤ cursor.val)
    (remaining : index.val + rows.length = total.val)
    (represented : NestedStorageRowsRepr primitive rows machine source index.val L)
    (fits : cursor.val + nestedStorageDemand rows < W) :
    NestedStorageLoopResult heap primitive rows base frame cursor machine source parent total index fits := by
  induction rows generalizing H heap base cursor machine index with
  | nil =>
    have same : index = total := Fin.ext (by simpa only [List.length_nil, Nat.add_zero] using remaining)
    subst index
    have iteration : loopIterN (run Objects.childrenCondition) (run nestedStorageTurnCode) (0 + 1)
        (nestedStorageControl machine source parent total total) =
        .inr (.ok (nestedStorageControl machine source parent total total) 0) := by
      rw [loopIterN, nested_storage_loop_done]
    unfold NestedStorageLoopResult
    simp only [nestedStorageValues, SVec.copyStToM_nil]
    refine ⟨base, machine, iteration, nested_storage_loop_run iteration, ?_, BaseExtends.refl base,
      gap, ?_, rfl, (fun _ _ _ _ => rfl), (fun _ _ kept _ => kept), Heap.Keeps.refl heap⟩
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
    have headRepr : ReprAt machine.store L (.ref (.array (.prim primitive))) (source.add index.val)
        (primitiveArrayValue primitive row.val row.property) := by
      simpa only [Nat.add_zero] using represented 0 row rfl
    obtain ⟨base1, machine1, body, allocated1, root, extension1, gap1, pointer, shape1, below1, gaps1, keeps1, id1, length1⟩ :=
      nested_storage_turn_success heap primitive row.val row.property base frame cursor machine source parent total index L
        allocator gap afterFrame beforeCursor more headRepr firstFits
    have nextIndex : wmod (index.val + 1) = index' := Fin.ext (Nat.mod_eq_of_lt nextBound)
    rw [nextIndex] at body
    have tailRepr : NestedStorageRowsRepr primitive rows machine1 source index'.val L := by
      intro offset selected chosen
      have stored : machine1.store = machine.store := by simpa only [] using congrArg Machine.store shape1
      rw [stored]
      have original : ReprAt machine.store L (.ref (.array (.prim primitive)))
          (source.add (index.val + (offset + 1))) (primitiveArrayValue primitive selected.val selected.property) :=
        represented (offset + 1) selected chosen
      simpa only [index', Nat.add_assoc, Nat.add_comm 1 offset] using original
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
    obtain ⟨base', target, tailIteration, tailRun, allocated, extension, finalGap, contents, shape, below, gaps, keeps⟩ :=
      ih first.heap base1 cursor' machine1 index' allocated1 gap1 beforeCursor' remaining' tailRepr tailFits
    let rest := (nestedStorageValues primitive rows).copyStToM first.heap rfl
    have iteration : loopIterN (run Objects.childrenCondition) (run nestedStorageTurnCode) ((row :: rows).length + 1)
        (nestedStorageControl machine source parent total index) =
        .inr (.ok (nestedStorageControl target source parent total total) 0) := by
      rw [List.length_cons, loopIterN, nested_storage_loop_more machine _ source parent total index more body]
      exact tailIteration
    have cursorEq : cursor'.val + nestedStorageDemand rows = cursor.val + nestedStorageDemand (row :: rows) := by
      simp only [cursor', nestedStorageDemand, Nat.add_assoc]
    have allKeeps : Heap.Keeps ((nestedStorageValues primitive (row :: rows)).copyStToM heap rfl).ext heap
        ((nestedStorageValues primitive (row :: rows)).copyStToM heap rfl).heap :=
      SVec.keeps_copyStToM _ rfl heap
    simp only [nestedStorageValues, SVec.copyStToM_cons] at allKeeps
    unfold NestedStorageLoopResult
    simp only [nestedStorageValues, SVec.copyStToM_cons]
    refine ⟨base', target, iteration, nested_storage_loop_run iteration, ?_,
      BaseExtends.trans first.ext extension1 extension, finalGap, ?_, ?_, ?_, ?_, allKeeps⟩
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

theorem nested_storage_loop_abort (machine : Machine) (source : Slot) (parent total index : Fin W)
    (more : index.val < total.val)
    (body : run nestedStorageTurnCode (nestedStorageControl machine source parent total index) = .revert) :
    loopTurn (run Objects.childrenCondition) (run nestedStorageTurnCode)
      (nestedStorageControl machine source parent total index) = .inr .revert := by
  have condition : run Objects.childrenCondition (nestedStorageControl machine source parent total index) =
      .ok ((nestedStorageControl machine source parent total index).push w[1]) 0 := by
    simpa only [nestedStorageControl, more, decide_true, bword] using
      Objects.childrenCondition_run (machine.push (.slot source)) parent total index
  rw [loopTurn, condition]
  change (if (1 : Nat) = 0 then _ else _) = _
  rw [if_neg (by decide)]
  simp only [Machine.push]
  rw [body]

theorem nested_storage_loop_refusal {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (parent total index : Fin W) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + total.val ≤ cursor.val)
    (remaining : index.val + rows.length = total.val)
    (represented : NestedStorageRowsRepr primitive rows machine source index.val L)
    (tooLarge : ¬ cursor.val + nestedStorageDemand rows < W) :
    loopIterN (run Objects.childrenCondition) (run nestedStorageTurnCode) (rows.length + 1)
        (nestedStorageControl machine source parent total index) = .inr .revert ∧
      run nestedStorageLoopCode (nestedStorageControl machine source parent total index) = .revert := by
  induction rows generalizing H heap base cursor machine index with
  | nil =>
    have room : cursor.val + nestedStorageDemand (primitive := primitive) [] < W := by
      simpa only [nestedStorageDemand, Nat.add_zero] using cursor.isLt
    exact (tooLarge room).elim
  | cons row rows ih =>
    have more : index.val < total.val := by simp only [List.length_cons] at remaining; omega
    have headRepr : ReprAt machine.store L (.ref (.array (.prim primitive))) (source.add index.val)
        (primitiveArrayValue primitive row.val row.property) := by
      simpa only [Nat.add_zero] using represented 0 row rfl
    by_cases firstFits : cursor.val + (row.val.length + 1) < W
    · let first := (primitiveArrayValue primitive row.val row.property).copyStToM heap rfl
      obtain ⟨base1, machine1, body, allocated, root, extension, gap1, pointer, shape, below, gaps, keeps, id, length⟩ :=
        nested_storage_turn_success heap primitive row.val row.property base frame cursor machine source parent total index L
          allocator gap afterFrame beforeCursor more headRepr firstFits
      have indexBound : index.val + 1 < W := Nat.lt_of_le_of_lt (by omega) total.isLt
      let index' : Fin W := ⟨index.val + 1, indexBound⟩
      let cursor' : Fin W := ⟨cursor.val + (row.val.length + 1), firstFits⟩
      have nextIndex : wmod (index.val + 1) = index' := Fin.ext (Nat.mod_eq_of_lt indexBound)
      rw [nextIndex] at body
      have tailRepr : NestedStorageRowsRepr primitive rows machine1 source index'.val L := by
        intro offset selected chosen
        have stored : machine1.store = machine.store := by simpa only [] using congrArg Machine.store shape
        rw [stored]
        have original : ReprAt machine.store L (.ref (.array (.prim primitive)))
            (source.add (index.val + (offset + 1))) (primitiveArrayValue primitive selected.val selected.property) :=
          represented (offset + 1) selected chosen
        simpa only [index', Nat.add_assoc, Nat.add_comm 1 offset] using original
      have tailTooLarge : ¬ cursor'.val + nestedStorageDemand rows < W := by
        change ¬ cursor.val + (row.val.length + 1) + nestedStorageDemand rows < W
        simpa only [nestedStorageDemand, Nat.add_assoc] using tooLarge
      obtain ⟨tailIteration, tailRun⟩ := ih first.heap base1 cursor' machine1 index' allocated gap1 (by
        change parent.val + 1 + total.val ≤ cursor.val + (row.val.length + 1)
        omega) (by
        change index.val + 1 + rows.length = total.val
        simp only [List.length_cons] at remaining
        omega) tailRepr tailTooLarge
      have iteration : loopIterN (run Objects.childrenCondition) (run nestedStorageTurnCode) ((row :: rows).length + 1)
          (nestedStorageControl machine source parent total index) = .inr .revert := by
        rw [List.length_cons, loopIterN, nested_storage_loop_more machine _ source parent total index more body]
        exact tailIteration
      exact ⟨iteration, nested_storage_loop_run iteration⟩
    · rcases nested_storage_turn_correct heap primitive row.val row.property base frame cursor machine source parent total index L
        allocator gap afterFrame beforeCursor more headRepr with success | refusal
      · exact (firstFits success.choose).elim
      · have iteration : loopIterN (run Objects.childrenCondition) (run nestedStorageTurnCode) ((row :: rows).length + 1)
            (nestedStorageControl machine source parent total index) = .inr .revert := by
          rw [List.length_cons, loopIterN, nested_storage_loop_abort machine source parent total index more refusal.2]
        exact ⟨iteration, nested_storage_loop_run iteration⟩

theorem nested_storage_loop_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (parent total index : Fin W) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (gap : Objects.Gap heap base parent.val (parent.val + 1 + total.val))
    (afterFrame : frame ≤ parent.val) (beforeCursor : parent.val + 1 + total.val ≤ cursor.val)
    (remaining : index.val + rows.length = total.val)
    (represented : NestedStorageRowsRepr primitive rows machine source index.val L) :
    (∃ fits, NestedStorageLoopResult heap primitive rows base frame cursor machine source parent total index fits) ∨
    (¬ cursor.val + nestedStorageDemand rows < W ∧
      loopIterN (run Objects.childrenCondition) (run nestedStorageTurnCode) (rows.length + 1)
        (nestedStorageControl machine source parent total index) = .inr .revert ∧
      run nestedStorageLoopCode (nestedStorageControl machine source parent total index) = .revert) := by
  by_cases fits : cursor.val + nestedStorageDemand rows < W
  · exact .inl ⟨fits, nested_storage_loop_success heap primitive rows base frame cursor machine source parent total index L
      allocator gap afterFrame beforeCursor remaining represented fits⟩
  · exact .inr ⟨fits, nested_storage_loop_refusal heap primitive rows base frame cursor machine source parent total index L
      allocator gap afterFrame beforeCursor remaining represented fits⟩

def nestedStorageLoop : NestedStorageLoopCertificate := ⟨nested_storage_loop_correct⟩

#print axioms nested_storage_loop_more
#print axioms nested_storage_loop_done
#print axioms nested_storage_loop_run
#print axioms nested_storage_loop_success
#print axioms nested_storage_loop_abort
#print axioms nested_storage_loop_refusal
#print axioms nested_storage_loop_correct
#print axioms nestedStorageLoop
end Solidity.Backend.MemoryCopies
