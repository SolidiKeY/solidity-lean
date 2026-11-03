import Solidity.Yul.Compilation.Allocation
import Solidity.Yul.Compilation.SlotSemantics

/-! Target-only prefix and finite-write preparation. Lists of indexed writes
are finite target data, not a Yul AST or V12 calling convention. Prefixes use
explicit top-first word order. Allocated offsets are not stack indices. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

/-- Concrete PUSH32 instructions, emitted bottom first for a top-first prefix. -/
def pushPrefix : Stack → Program
  | [] => []
  | x :: xs => pushPrefix xs ++ [pushWord x]

def popPrefix : Nat → Program
  | 0 => []
  | n + 1 => .op .POP :: popPrefix n

theorem pushPrefix_run (xs tail : Stack) :
    run (pushPrefix xs) tail = some (xs ++ tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [pushPrefix, run_append, ih]
    simp only [Option.bind_some, run, step_pushWord]
    rfl

theorem popPrefix_run (xs tail : Stack) :
    run (popPrefix xs.length) (xs ++ tail) = some tail := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, popPrefix, List.cons_append, run, step, pop,
      Option.bind_some]
    exact ih

/-- Arity-indexed entry and removal, not a function-entry convention. -/
theorem prefix_roundtrip {n : Nat} (xs : Vector Word n) (tail : Stack) :
    run (pushPrefix xs.toList ++ popPrefix n) tail = some tail := by
  apply run_comp (pushPrefix_run xs.toList tail)
  simpa only [Vector.length_toList] using popPrefix_run xs.toList tail

/-- Replace an explicitly supplied argument prefix with explicit result data.
No return address, jump or source call is represented. -/
theorem prefix_replace {a r : Nat} (args : Vector Word a) (results : Vector Word r)
    (tail : Stack) :
    run (popPrefix a ++ pushPrefix results.toList) (args.toList ++ tail) =
      some (results.toList ++ tail) := by
  apply run_comp (t := tail)
  · simpa only [Vector.length_toList] using popPrefix_run args.toList tail
  · exact pushPrefix_run results.toList tail

theorem nested_prefix {a b : Nat} (outer : Vector Word a) (inner : Vector Word b)
    (tail : Stack) :
    run (pushPrefix outer.toList ++ pushPrefix inner.toList ++ popPrefix b)
      tail = some (outer.toList ++ tail) := by
  apply run_comp
  · exact run_comp (pushPrefix_run outer.toList tail)
      (pushPrefix_run inner.toList (outer.toList ++ tail))
  · simpa only [Vector.length_toList] using
      popPrefix_run inner.toList (outer.toList ++ tail)

/-- Every write index intrinsically inhabits the finite locals and actual
SWAP range; a supplied word is emitted using the existing concrete PUSH32. -/
abbrev LocalWrites (n : Nat) := List ({i : Fin n // i.val < 16} × Word)

def writeSequence {n : Nat} : LocalWrites n → Program
  | [] => []
  | (i, value) :: rest => [pushWord value] ++
      writeSlot ⟨i.val.val, i.property⟩ ++ writeSequence rest

def updatedLocals {n : Nat} (locals : Vector Word n) : LocalWrites n → Vector Word n
  | [] => locals
  | (i, value) :: rest => updatedLocals (locals.set i.val.val value i.val.isLt) rest

/-- Constructive final contents for any finite sequence, including repeated slots. -/
theorem writeSequence_run {n : Nat} (writes : LocalWrites n)
    (locals : Vector Word n) (tail : Stack) :
    run (writeSequence writes) (locals.toList ++ tail) =
      some ((updatedLocals locals writes).toList ++ tail) := by
  induction writes generalizing locals with
  | nil => rfl
  | cons w rest ih =>
    rcases w with ⟨i, value⟩
    simp only [writeSequence, updatedLocals]
    apply run_comp
    · apply run_comp (t := value :: (locals.toList ++ tail))
      · simp only [run, step_pushWord, Option.bind_some]
      · exact write_local locals i.val i.property value tail
    · exact ih _

theorem writeSequence_caller {n : Nat} (writes : LocalWrites n)
    (locals : Vector Word n) (tail : Stack) :
    (run (writeSequence writes) (locals.toList ++ tail)).map (List.drop n) =
      some tail := by
  rw [writeSequence_run]
  simp only [Option.map_some]
  exact congrArg some (List.drop_left' Vector.length_toList)

/-- Enter a finite prefix, run arbitrary bounded-index updates, then remove it.
The caller contents survive the entire actual instruction sequence. -/
theorem scope_updates_exit {n : Nat} (locals : Vector Word n)
    (writes : LocalWrites n) (tail : Stack) :
    run (pushPrefix locals.toList ++ writeSequence writes ++ popPrefix n) tail =
      some tail := by
  apply run_comp
  · exact run_comp (pushPrefix_run locals.toList tail)
      (writeSequence_run writes locals tail)
  · simpa only [Vector.length_toList] using
      popPrefix_run (updatedLocals locals writes).toList tail

/-- Stack capacity is a separate actual height-trace premise. -/
theorem writeSequence_capacity {n : Nat} (writes : LocalWrites n)
    (locals : Vector Word n) (tail : Stack)
    (bounded : stackBound (writeSequence writes) ((n + tail.length : Nat) : Int) = true) :
    n + tail.length ≤ 1024 := by
  have h := run_capacity (writeSequence_run writes locals tail)
  simp only [List.length_append, Vector.length_toList] at h
  exact h bounded

/-- Allocation coordinates convert to a live depth only at an explicit height.
After k newer binders, the original local is at depth k+i, not at s.at i. -/
theorem Slots.live_depth {n : Nat} (s : Slots n) (i : Fin n) (k : Nat) :
    (s.base + n + k - 1) - s.at i = k + i.val := by
  have hi : i.val < n := i.isLt
  simp only [Slots.at]
  omega

/-- At the stated height the live depth can use DUP/SWAP iff it is below16. -/
theorem Slots.live_accessible {n : Nat} (s : Slots n) (i : Fin n) (k : Nat) :
    (s.base + n + k - 1) - s.at i < 16 ↔ k + i.val < 16 := by
  rw [Slots.live_depth]

/-- Removing too many words fails, rather than synthesizing a caller prefix. -/
theorem popPrefix_underflow (xs : Stack) (n : Nat) (short : xs.length < n) :
    run (popPrefix n) xs = none := by
  induction n generalizing xs with
  | zero => omega
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      have h : xs.length < n := by simp only [List.length_cons] at short; omega
      simp only [popPrefix, run, step, pop, Option.bind_some]
      exact ih xs h

/-- Finite updates compose constructively in their execution order. -/
theorem updatedLocals_append {n : Nat} (locals : Vector Word n)
    (first second : LocalWrites n) :
    updatedLocals locals (first ++ second) =
      updatedLocals (updatedLocals locals first) second := by
  induction first generalizing locals with
  | nil => rfl
  | cons w rest ih =>
    rcases w with ⟨i, value⟩
    simp only [List.cons_append, updatedLocals, ih]

theorem writeSequence_append {n : Nat} (first second : LocalWrites n) :
    writeSequence (first ++ second) = writeSequence first ++ writeSequence second := by
  induction first with
  | nil => rfl
  | cons w rest ih =>
    rcases w with ⟨i, value⟩
    simp only [List.cons_append, writeSequence, ih, List.append_assoc]

/-- Last write to the same local wins, for arbitrary full words. -/
theorem writeSequence_same {n : Nat} (locals : Vector Word n)
    (i : {i : Fin n // i.val < 16}) (a b : Word) (tail : Stack) :
    run (writeSequence [(i, a), (i, b)]) (locals.toList ++ tail) =
      some ((locals.set i.val.val b i.val.isLt).toList ++ tail) := by
  rw [writeSequence_run]
  simp only [updatedLocals, Vector.set_set]

/-- Independent constant local writes commute; this says nothing about
expressions/effects whose computed values might depend on an earlier write. -/
theorem writeSequence_distinct_commute {n : Nat} (locals : Vector Word n)
    (i j : {i : Fin n // i.val < 16}) (different : i.val ≠ j.val)
    (a b : Word) (tail : Stack) :
    run (writeSequence [(i, a), (j, b)]) (locals.toList ++ tail) =
      run (writeSequence [(j, b), (i, a)]) (locals.toList ++ tail) := by
  rw [writeSequence_run, writeSequence_run]
  simp only [updatedLocals]
  have hne : i.val.val ≠ j.val.val := fun h => different (Fin.ext h)
  rw [Vector.set_comm a b hne]

/-- Reads of an old local under a newer prefix use the shifted live depth. -/
theorem read_under_prefix {n k : Nat} (locals : Vector Word n)
    (newer : Vector Word k) (i : Fin n) (accessible : k + i.val < 16)
    (tail : Stack) :
    step (readSlot ⟨k + i.val, accessible⟩)
      (newer.toList ++ (locals.toList ++ tail)) =
      some (locals[i.val] :: (newer.toList ++ (locals.toList ++ tail))) := by
  apply readSlot_correct
  rw [List.getElem?_append_right (show newer.toList.length ≤ k + i.val by
    simp only [Vector.length_toList]; omega)]
  simp only [Vector.length_toList, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [Vector.length_toList] using i.isLt)]
  simp only [Vector.getElem?_toList, Vector.getElem?_eq_getElem i.isLt]

/-- The numeric allocation formula supplies the explicit live-depth equality
for the preceding target theorem. Caller length must equal allocation base. -/
theorem read_at_allocated_depth {n k : Nat} (s : Slots n) (locals : Vector Word n)
    (newer : Vector Word k) (i : Fin n) (tail : Stack)
    (base_matches : tail.length = s.base)
    (accessible : k + i.val < 16) :
    ∃ depth : Fin 16,
      depth.val = (tail.length + n + k - 1) - s.at i ∧
      step (readSlot depth) (newer.toList ++ (locals.toList ++ tail)) =
        some (locals[i.val] :: (newer.toList ++ (locals.toList ++ tail))) := by
  refine ⟨⟨k + i.val, accessible⟩, ?_, read_under_prefix locals newer i accessible tail⟩
  rw [base_matches, Slots.live_depth]

/-- Arity replacement capacity remains a real trace obligation, not run success. -/
theorem prefix_replace_capacity {a r : Nat} (args : Vector Word a)
    (results : Vector Word r) (tail : Stack)
    (bounded : stackBound (popPrefix a ++ pushPrefix results.toList)
      ((a + tail.length : Nat) : Int) = true) : r + tail.length ≤ 1024 := by
  have h := run_capacity (prefix_replace args results tail)
  simp only [List.length_append, Vector.length_toList] at h
  exact h bounded

/-- Every nonempty write sequence temporarily needs one extra stack word. -/
theorem writeSequence_bound_necessary {n : Nat}
    (first : {i : Fin n // i.val < 16} × Word) (rest : LocalWrites n) (height : Nat)
    (bounded : stackBound (writeSequence (first :: rest)) (height : Int) = true) :
    height + 1 ≤ 1024 := by
  rcases first with ⟨i, value⟩
  simp only [writeSequence, writeSlot, pushWord, List.cons_append, List.nil_append,
    stackBound, heightTrace, stackDelta, List.all_cons, Bool.and_eq_true,
    safeHeight, decide_eq_true_eq] at bounded
  omega

/-- A spare word suffices for the actual height trace of any finite sequence.
Operand existence still comes from the intrinsic local bounds in run's law. -/
theorem writeSequence_bound_sufficient {n : Nat} (writes : LocalWrites n)
    (height : Int) (low : 0 ≤ height) (high : height + 1 ≤ 1024) :
    stackBound (writeSequence writes) height = true := by
  induction writes with
  | nil =>
    simp only [writeSequence, stackBound, heightTrace, List.all_cons,
      List.all_nil, Bool.and_true, safeHeight, decide_eq_true_eq]
    omega
  | cons w rest ih =>
    rcases w with ⟨i, value⟩
    have cancel : height + 1 + -1 = height := by omega
    simp only [stackBound] at ih
    simp only [writeSequence, writeSlot, pushWord, List.cons_append, List.nil_append,
      stackBound, heightTrace, stackDelta, Int.add_zero, cancel, List.all_cons,
      Bool.and_eq_true, safeHeight, decide_eq_true_eq]
    exact ⟨⟨low, by omega⟩, ⟨⟨by omega, high⟩, ⟨⟨by omega, high⟩, ih⟩⟩⟩

#print axioms pushPrefix_run
#print axioms popPrefix_run
#print axioms prefix_roundtrip
#print axioms prefix_replace
#print axioms nested_prefix
#print axioms writeSequence_run
#print axioms writeSequence_caller
#print axioms scope_updates_exit
#print axioms writeSequence_capacity
#print axioms Slots.live_depth
#print axioms Slots.live_accessible
#print axioms popPrefix_underflow

#print axioms updatedLocals_append
#print axioms writeSequence_append
#print axioms writeSequence_distinct_commute
#print axioms writeSequence_same
#print axioms read_under_prefix
#print axioms read_at_allocated_depth
#print axioms prefix_replace_capacity
#print axioms writeSequence_bound_sufficient
#print axioms writeSequence_bound_necessary
end Solidity.Yul.Compilation
