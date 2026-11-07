import Solidity.Yul.Compilation.Slices

/-! Guard treating a valid DUP/SWAP index as an existing stack cell, assuming an
exchange result instead of deriving it, or losing the prefix/caller tail during
slot writeback. Extend the existing readSlot/writeSlot API for every accessible
prefix and arbitrary full-width words. Numeric-slice semantics only: the
existing1024-word prefix bound is checked separately from operand presence.
Gas, Source/G24 simulation and native adequacy remain separate obligations. No new instruction or per-shape interface is defined. -/
namespace Solidity.Yul.Compilation
open Backend Backend.Scalar

/-- Derive the actual exchange from the stack's prefix/selected-cell/tail split. -/
theorem exchange_prefix (value old : Word) (pre tail : Stack) :
    exchange value pre.length (pre ++ old :: tail) =
      some (old, pre ++ value :: tail) := by
  induction pre with
  | nil => rfl
  | cons top pre ih =>
    change (exchange value pre.length (pre ++ old :: tail)).map
      (fun pair => (pair.1, top :: pair.2)) = _
    rw [ih]
    rfl

theorem readSlot_prefix (pre : Stack) (value : Word) (tail : Stack)
    (accessible : pre.length < 16) :
    step (readSlot ⟨pre.length, accessible⟩) (pre ++ value :: tail) =
      some (value :: (pre ++ value :: tail)) := by
  apply readSlot_correct
  change (pre ++ value :: tail)[pre.length]? = some value
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

theorem writeSlot_prefix (value old : Word) (pre tail : Stack)
    (accessible : pre.length < 16) :
    run (writeSlot ⟨pre.length, accessible⟩)
      (value :: (pre ++ old :: tail)) = some (pre ++ value :: tail) :=
  writeSlot_correct ⟨pre.length, accessible⟩ value old _ _
    (exchange_prefix value old pre tail)

/-- DUP followed by writeback of the selected value is the actual identity run. -/
theorem read_writeSlot_prefix (pre : Stack) (value : Word) (tail : Stack)
    (accessible : pre.length < 16) :
    run ([readSlot ⟨pre.length, accessible⟩] ++
      writeSlot ⟨pre.length, accessible⟩) (pre ++ value :: tail) =
      some (pre ++ value :: tail) := by
  have read : run [readSlot ⟨pre.length, accessible⟩]
      (pre ++ value :: tail) = some (value :: (pre ++ value :: tail)) := by
    change (step (readSlot ⟨pre.length, accessible⟩)
      (pre ++ value :: tail)).bind (run []) = _
    rw [readSlot_prefix pre value tail accessible]
    rfl
  exact run_comp read (writeSlot_prefix value value pre tail accessible)

/-- An opcode-range proof cannot fabricate the cell at the end of a stack. -/
theorem exchange_at_end (value : Word) (stack : Stack) :
    exchange value stack.length stack = none := by
  induction stack with
  | nil => rfl
  | cons top stack ih =>
    change (exchange value stack.length stack).map _ = none
    rw [ih]
    rfl

theorem readSlot_at_end (stack : Stack) (accessible : stack.length < 16) :
    step (readSlot ⟨stack.length, accessible⟩) stack = none := by
  change (stack[stack.length]?).map (fun value => value :: stack) = none
  rw [List.getElem?_eq_none (Nat.le_refl _)]
  rfl

theorem writeSlot_at_end (value : Word) (stack : Stack)
    (accessible : stack.length < 16) :
    run (writeSlot ⟨stack.length, accessible⟩) (value :: stack) = none := by
  simp only [writeSlot, run, step, swap, exchange_at_end,
    Option.map_none, Option.bind_none]

/-- A nonzero slot preserves the preceding cell and every caller tail, then
read/writeback is a genuine successful identity on the same split. -/
theorem stack_slot_witness (tail : Stack) :
    run (writeSlot ⟨1, by decide⟩) (7 :: 10 :: 20 :: tail) =
      some (10 :: 7 :: tail) ∧
    run ([readSlot ⟨1, by decide⟩] ++ writeSlot ⟨1, by decide⟩)
      (10 :: 20 :: tail) = some (10 :: 20 :: tail) :=
  ⟨writeSlot_prefix 7 20 [10] tail (by decide),
    read_writeSlot_prefix [10] 20 tail (by decide)⟩

/-- DUP checks both entry and the temporary extra word. Height bounds alone
say nothing about the indexed operand's existence. -/
theorem readSlot_bound_iff (i : Fin 16) (height : Int) :
    stackBound [readSlot i] height = true ↔
      0 ≤ height ∧ height + 1 ≤ 1024 := by
  change (safeHeight height && (safeHeight (height + 1) && true)) = true ↔ _
  rw [Bool.and_true, Bool.and_eq_true, safeHeight, decide_eq_true_eq,
    safeHeight, decide_eq_true_eq]
  omega

/-- Although read/writeback has zero final delta, its DUP prefix needs one word
of headroom. This preserves the original1024 bound at every instruction edge. -/
theorem read_writeSlot_bound_iff (i : Fin 16) (height : Int) :
    stackBound ([readSlot i] ++ writeSlot i) height = true ↔
      0 ≤ height ∧ height + 1 ≤ 1024 := by
  have same : stackBound ([readSlot i] ++ writeSlot i) height =
      stackBound [readSlot i] height := by
    change (safeHeight height && (safeHeight (height + 1) &&
      (safeHeight (height + 1 + 0) &&
      (safeHeight (height + 1 + 0 + -1) && true)))) =
      (safeHeight height && (safeHeight (height + 1) && true))
    have back : height + 1 + -1 = height := by omega
    rw [Int.add_zero, back]
    cases safeHeight height <;> cases safeHeight (height + 1) <;> rfl
  rw [same]
  exact readSlot_bound_iff i height

/-- Joint actual execution and every-prefix height check for the same stack. -/
theorem read_writeSlot_safe (pre : Stack) (value : Word) (tail : Stack)
    (accessible : pre.length < 16)
    (headroom : pre.length + 1 + tail.length < 1024) :
    run ([readSlot ⟨pre.length, accessible⟩] ++
      writeSlot ⟨pre.length, accessible⟩) (pre ++ value :: tail) =
      some (pre ++ value :: tail) ∧
    stackBound ([readSlot ⟨pre.length, accessible⟩] ++
      writeSlot ⟨pre.length, accessible⟩)
      ((pre ++ value :: tail).length : Int) = true := by
  refine ⟨read_writeSlot_prefix pre value tail accessible, ?_⟩
  apply (read_writeSlot_bound_iff _ _).mpr
  simp only [List.length_append, List.length_cons]
  omega

theorem read_writeSlot_overflow (i : Fin 16) :
    stackBound ([readSlot i] ++ writeSlot i) 1024 = false := by
  cases bound : stackBound ([readSlot i] ++ writeSlot i) 1024 with
  | false => rfl
  | true =>
    have impossible := (read_writeSlot_bound_iff i 1024).mp bound
    omega

/-- A final-height-only argument would accept this successful mathematical
identity, but the actual prefix bound rejects its temporary1025-word stack. -/
theorem full_stack_counterexample (value : Word) (tail : Stack)
    (full : tail.length = 1023) :
    run ([readSlot ⟨0, by decide⟩] ++ writeSlot ⟨0, by decide⟩)
      (value :: tail) = some (value :: tail) ∧
    stackBound ([readSlot ⟨0, by decide⟩] ++ writeSlot ⟨0, by decide⟩)
      ((value :: tail).length : Int) = false := by
  refine ⟨read_writeSlot_prefix [] value tail (by decide), ?_⟩
  simp only [List.length_cons, full]
  exact read_writeSlot_overflow ⟨0, by decide⟩

/-- A passing height check cannot stand in for the successful operand law. -/
theorem capacity_without_operand :
    stackBound [readSlot ⟨0, by decide⟩] 0 = true ∧
    step (readSlot ⟨0, by decide⟩) [] = none :=
  ⟨(readSlot_bound_iff _ 0).mpr (by decide), readSlot_at_end [] (by decide)⟩

theorem bounded_slot_witness :
    run ([readSlot ⟨1, by decide⟩] ++ writeSlot ⟨1, by decide⟩)
      [10,20,99] = some [10,20,99] ∧
    stackBound ([readSlot ⟨1, by decide⟩] ++ writeSlot ⟨1, by decide⟩) 3 = true :=
  read_writeSlot_safe [10] 20 [99] (by decide) (by decide)

/-- info: 'Solidity.Yul.Compilation.exchange_prefix' does not depend on any axioms -/
#guard_msgs in
#print axioms exchange_prefix
/-- info: 'Solidity.Yul.Compilation.readSlot_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readSlot_prefix
/-- info: 'Solidity.Yul.Compilation.writeSlot_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writeSlot_prefix
/-- info: 'Solidity.Yul.Compilation.read_writeSlot_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms read_writeSlot_prefix
/-- info: 'Solidity.Yul.Compilation.exchange_at_end' does not depend on any axioms -/
#guard_msgs in
#print axioms exchange_at_end
/-- info: 'Solidity.Yul.Compilation.readSlot_at_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readSlot_at_end
/-- info: 'Solidity.Yul.Compilation.writeSlot_at_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writeSlot_at_end
/-- info: 'Solidity.Yul.Compilation.stack_slot_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stack_slot_witness
/-- info: 'Solidity.Yul.Compilation.readSlot_bound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms readSlot_bound_iff
/-- info: 'Solidity.Yul.Compilation.read_writeSlot_bound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms read_writeSlot_bound_iff
/-- info: 'Solidity.Yul.Compilation.read_writeSlot_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms read_writeSlot_safe
/-- info: 'Solidity.Yul.Compilation.read_writeSlot_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms read_writeSlot_overflow
/-- info: 'Solidity.Yul.Compilation.full_stack_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms full_stack_counterexample
/-- info: 'Solidity.Yul.Compilation.capacity_without_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms capacity_without_operand
/-- info: 'Solidity.Yul.Compilation.bounded_slot_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bounded_slot_witness
end Solidity.Yul.Compilation
