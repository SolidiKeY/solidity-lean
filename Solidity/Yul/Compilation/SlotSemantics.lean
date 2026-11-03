import Solidity.Yul.Compilation.Slices

/-!
# Concrete finite-local stack slots

Target-only laws for the existing scalar executor. Finite locals occupy the
stack prefix, newest/top first; the caller tail is arbitrary. No source state,
AST or runtime calling convention is introduced. The finite index bounds
supply exchange success, rather than assuming the desired update result.
-/
namespace Solidity.Yul.Compilation
open Backend Scalar

/-- The existing exchange computes the ordinary list update at any valid index. -/
theorem exchange_set (value : Word) (xs : Stack) (i : Nat) (hi : i < xs.length) :
    exchange value i xs = some (xs[i], xs.set i value) := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => cases hi
    | cons x xs => rfl
  | succ i ih =>
    cases xs with
    | nil => cases hi
    | cons x xs =>
      have h : i < xs.length := by simp only [List.length_cons] at hi; omega
      simp only [exchange, ih xs h, Option.map_some, List.set_cons_succ,
        List.getElem_cons_succ]

/-- DUP's lookup follows from the intrinsic local index; the tail is retained. -/
theorem read_local {n : Nat} (locals : Vector Word n) (i : Fin n)
    (accessible : i.val < 16) (caller : Stack) :
    step (readSlot ⟨i.val, accessible⟩) (locals.toList ++ caller) =
      some (locals[i.val] :: (locals.toList ++ caller)) := by
  apply readSlot_correct
  rw [List.getElem?_append_left (by simpa only [Vector.length_toList] using i.isLt)]
  simp only [Vector.getElem?_toList, Vector.getElem?_eq_getElem i.isLt]

theorem read_local_height {n : Nat} (locals : Vector Word n) (i : Fin n)
    (accessible : i.val < 16) (caller : Stack) :
    (step (readSlot ⟨i.val, accessible⟩) (locals.toList ++ caller)).map
      List.length = some (n + caller.length + 1) := by
  rw [read_local]
  simp only [Option.map_some, List.length_cons, List.length_append, Vector.length_toList]

/-- SWAP/POP updates exactly one local and preserves every caller word. -/
theorem write_local {n : Nat} (locals : Vector Word n) (i : Fin n)
    (accessible : i.val < 16) (value : Word) (caller : Stack) :
    run (writeSlot ⟨i.val, accessible⟩) (value :: (locals.toList ++ caller)) =
      some ((locals.set i.val value i.isLt).toList ++ caller) := by
  have hi : i.val < locals.toList.length := by
    simpa only [Vector.length_toList] using i.isLt
  have h := exchange_frame value i.val (exchange_set value locals.toList i.val hi) caller
  exact writeSlot_correct ⟨i.val, accessible⟩ value (locals.toList[i.val]'hi)
    (locals.toList ++ caller) ((locals.set i.val value i.isLt).toList ++ caller)
    (by simpa only [Vector.toList_set] using h)

/-- A local write changes the stack height only by consuming its value word. -/
theorem write_local_height {n : Nat} (locals : Vector Word n) (i : Fin n)
    (accessible : i.val < 16) (value : Word) (caller : Stack) :
    (run (writeSlot ⟨i.val, accessible⟩) (value :: (locals.toList ++ caller))).map
      List.length = some (n + caller.length) := by
  rw [write_local]
  simp only [Option.map_some, List.length_append, Vector.length_toList]

/-- Dropping the finite local prefix after execution recovers the exact caller. -/
theorem write_local_caller {n : Nat} (locals : Vector Word n) (i : Fin n)
    (accessible : i.val < 16) (value : Word) (caller : Stack) :
    (run (writeSlot ⟨i.val, accessible⟩) (value :: (locals.toList ++ caller))).map
      (List.drop n) = some caller := by
  rw [write_local]
  simp only [Option.map_some]
  exact congrArg some (List.drop_left' Vector.length_toList)

/-- Every nonselected local survives, including locals deeper than DUP16. -/
theorem write_local_other {n : Nat} (locals : Vector Word n) (i j : Fin n)
    (accessible : i.val < 16) (different : i ≠ j) (value : Word) (caller : Stack) :
    (run (writeSlot ⟨i.val, accessible⟩) (value :: (locals.toList ++ caller))).map
      (fun stack => stack[j.val]?) = some (some locals[j.val]) := by
  have hne : i.val ≠ j.val := fun h => different (Fin.ext h)
  rw [write_local]
  simp only [Option.map_some, List.getElem?_append_left
    (show j.val < (locals.set i.val value i.isLt).toList.length by
      simpa only [Vector.length_toList] using j.isLt), Vector.getElem?_toList,
    Vector.getElem?_set_ne i.isLt hne, Vector.getElem?_eq_getElem j.isLt]

/-- Execute the real SWAP/POP followed by the real DUP, with no cleaning. -/
theorem read_after_write_local {n : Nat} (locals : Vector Word n) (i : Fin n)
    (accessible : i.val < 16) (value : Word) (caller : Stack) :
    run (writeSlot ⟨i.val, accessible⟩ ++ [readSlot ⟨i.val, accessible⟩])
      (value :: (locals.toList ++ caller)) =
      some (value :: ((locals.set i.val value i.isLt).toList ++ caller)) := by
  rw [run_append, write_local]
  simp only [Option.bind_some, run]
  rw [read_local, Vector.getElem_set_self]
  rfl

/-- Reading a different accessible local after a write returns its original word. -/
theorem read_other_after_write_local {n : Nat} (locals : Vector Word n) (i j : Fin n)
    (accessibleI : i.val < 16) (accessibleJ : j.val < 16)
    (different : i ≠ j) (value : Word) (caller : Stack) :
    run (writeSlot ⟨i.val, accessibleI⟩ ++ [readSlot ⟨j.val, accessibleJ⟩])
      (value :: (locals.toList ++ caller)) =
      some (locals[j.val] :: ((locals.set i.val value i.isLt).toList ++ caller)) := by
  have hne : i.val ≠ j.val := fun h => different (Fin.ext h)
  rw [run_append, write_local]
  simp only [Option.bind_some, run]
  rw [read_local, Vector.getElem_set_ne i.isLt j.isLt hne]
  rfl

/-- Capacity is checked on the actual opcode-height trace, separately from run.
This includes the extra input value before SWAP/POP. -/
theorem write_local_bound_iff (n : Nat) (i : Fin 16) (caller : Stack) :
    stackBound (writeSlot i) ((n + caller.length + 1 : Nat) : Int) = true ↔
      n + caller.length + 1 ≤ 1024 := by
  simp only [writeSlot, stackBound, heightTrace, stackDelta, safeHeight,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem read_local_bound_iff (n : Nat) (i : Fin 16) (caller : Stack) :
    stackBound [readSlot i] ((n + caller.length : Nat) : Int) = true ↔
      n + caller.length + 1 ≤ 1024 := by
  simp only [readSlot, stackBound, heightTrace, stackDelta, safeHeight,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- Local success is unconditional on capacity; the capacity conclusion is not. -/
theorem write_local_capacity {n : Nat} (locals : Vector Word n) (i : Fin n)
    (accessible : i.val < 16) (value : Word) (caller : Stack)
    (capacity : stackBound (writeSlot ⟨i.val, accessible⟩)
      ((n + caller.length + 1 : Nat) : Int) = true) : n + caller.length ≤ 1024 := by
  have h := run_capacity (write_local locals i accessible value caller)
  simp only [List.length_cons, List.length_append, Vector.length_toList] at h
  exact h capacity

/-- An out-of-range exchange fails in the actual partial scalar executor. -/
theorem exchange_out_of_range (value : Word) (xs : Stack) (i : Nat)
    (outside : xs.length ≤ i) : exchange value i xs = none := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [List.length_cons] at outside; omega
  | succ i ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      have h : xs.length ≤ i := by simp only [List.length_cons] at outside; omega
      simp only [exchange, ih xs h, Option.map_none]

theorem write_slot_underflow (i : Fin 16) (value : Word) (stack : Stack)
    (outside : stack.length ≤ i.val) : run (writeSlot i) (value :: stack) = none := by
  simp only [writeSlot, run, step, swap, exchange_out_of_range value stack i.val outside,
    Option.map_none, Option.bind_none]

#print axioms read_local_height
#print axioms write_local_height
#print axioms read_local_bound_iff
#print axioms exchange_out_of_range
#print axioms write_slot_underflow
#print axioms write_local_caller
#print axioms write_local_other
#print axioms read_after_write_local
#print axioms read_other_after_write_local
#print axioms write_local_bound_iff
#print axioms write_local_capacity
#print axioms exchange_set
#print axioms read_local
#print axioms write_local
end Solidity.Yul.Compilation
