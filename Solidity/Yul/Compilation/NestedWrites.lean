import Solidity.Yul.Compilation.ScopeSemantics

/-! Target-only old-local writes below fixed newer words. Finite write data
is intrinsically bounded; allocation coordinates remain distinct from depths.
No source AST, frame convention or prerequisite runtime is introduced. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

theorem write_under_prefix {n k : Nat} (locals : Vector Word n)
    (newer : Vector Word k) (i : Fin n) (accessible : k + i.val < 16)
    (value : Word) (tail : Stack) :
    run (writeSlot ⟨k + i.val, accessible⟩)
      (value :: (newer.toList ++ (locals.toList ++ tail))) =
      some (newer.toList ++ ((locals.set i.val value i.isLt).toList ++ tail)) := by
  have hi : k + i.val < k + n := by have h : i.val < n := i.isLt; omega
  simpa only [Vector.set_append_right hi (by omega), Nat.add_sub_cancel_left,
    Vector.toList_append, List.append_assoc] using
    (write_local (newer ++ locals) ⟨k + i.val, hi⟩ accessible value tail)

theorem read_after_write_under_prefix {n k : Nat} (locals : Vector Word n)
    (newer : Vector Word k) (i : Fin n) (accessible : k + i.val < 16)
    (value : Word) (tail : Stack) :
    run (writeSlot ⟨k + i.val, accessible⟩ ++ [readSlot ⟨k + i.val, accessible⟩])
      (value :: (newer.toList ++ (locals.toList ++ tail))) =
      some (value :: (newer.toList ++ ((locals.set i.val value i.isLt).toList ++ tail))) := by
  rw [run_append, write_under_prefix]
  simp only [Option.bind_some, run]
  rw [read_under_prefix, Vector.getElem_set_self]
  rfl

theorem read_other_after_write_under_prefix {n k : Nat} (locals : Vector Word n)
    (newer : Vector Word k) (i j : Fin n) (ai : k + i.val < 16)
    (aj : k + j.val < 16) (different : i ≠ j) (value : Word) (tail : Stack) :
    run (writeSlot ⟨k + i.val, ai⟩ ++ [readSlot ⟨k + j.val, aj⟩])
      (value :: (newer.toList ++ (locals.toList ++ tail))) =
      some (locals[j.val] ::
        (newer.toList ++ ((locals.set i.val value i.isLt).toList ++ tail))) := by
  have hne : i.val ≠ j.val := fun h => different (Fin.ext h)
  rw [run_append, write_under_prefix]
  simp only [Option.bind_some, run]
  rw [read_under_prefix, Vector.getElem_set_ne i.isLt j.isLt hne]
  rfl

/-- Nonselected old locals survive, even when not themselves DUP-accessible. -/
theorem write_under_prefix_other {n k : Nat} (locals : Vector Word n)
    (newer : Vector Word k) (i j : Fin n) (ai : k + i.val < 16)
    (different : i ≠ j) (value : Word) (tail : Stack) :
    (run (writeSlot ⟨k + i.val, ai⟩)
      (value :: (newer.toList ++ (locals.toList ++ tail)))).map
        (fun stack => stack[k + j.val]?) = some (some locals[j.val]) := by
  have hne : i.val ≠ j.val := fun h => different (Fin.ext h)
  rw [write_under_prefix]
  simp only [Option.map_some, List.getElem?_append_right
    (show newer.toList.length ≤ k + j.val by simp only [Vector.length_toList]; omega),
    Vector.length_toList, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [Vector.length_toList] using j.isLt)]
  simp only [Vector.getElem?_toList, Vector.getElem?_set_ne i.isLt hne,
    Vector.getElem?_eq_getElem j.isLt]

/-- Only finite target data; both old-local and shifted physical bounds are intrinsic. -/
abbrev NestedWrites (n k : Nat) := List ({i : Fin n // k + i.val < 16} × Word)

def oldWrites {n k : Nat} (writes : NestedWrites n k) : LocalWrites n :=
  writes.map (fun (i, v) => (⟨i.val, by have h : k + i.val.val < 16 := i.property; omega⟩, v))

def shiftedWrites {n k : Nat} (writes : NestedWrites n k) : LocalWrites (k + n) :=
  writes.map (fun (i, v) =>
    (⟨⟨k + i.val.val, by have h : i.val.val < n := i.val.isLt; omega⟩, i.property⟩, v))

theorem nested_writes_run {n k : Nat} (writes : NestedWrites n k)
    (locals : Vector Word n) (newer : Vector Word k) (tail : Stack) :
    run (writeSequence (shiftedWrites writes)) (newer.toList ++ (locals.toList ++ tail)) =
      some (newer.toList ++ ((updatedLocals locals (oldWrites writes)).toList ++ tail)) := by
  induction writes generalizing locals with
  | nil => rfl
  | cons w rest ih =>
    rcases w with ⟨i, value⟩
    simp only [shiftedWrites, oldWrites, List.map_cons, writeSequence, updatedLocals]
    apply run_comp
    · apply run_comp (t := value :: (newer.toList ++ (locals.toList ++ tail)))
      · simp only [run, step_pushWord, Option.bind_some]
      · exact write_under_prefix locals newer i.val i.property value tail
    · exact ih _

/-- Read back any accessible old local after the finite update sequence. -/
theorem nested_writes_read {n k : Nat} (writes : NestedWrites n k)
    (locals : Vector Word n) (newer : Vector Word k) (j : Fin n)
    (accessible : k + j.val < 16) (tail : Stack) :
    run (writeSequence (shiftedWrites writes) ++ [readSlot ⟨k + j.val, accessible⟩])
      (newer.toList ++ (locals.toList ++ tail)) =
      some ((updatedLocals locals (oldWrites writes))[j.val] ::
        (newer.toList ++ ((updatedLocals locals (oldWrites writes)).toList ++ tail))) := by
  rw [run_append, nested_writes_run]
  simp only [Option.bind_some, run]
  rw [read_under_prefix]
  rfl

/-- Removal leaves the exact caller, irrespective of any sequence contents. -/
theorem nested_writes_caller {n k : Nat} (writes : NestedWrites n k)
    (locals : Vector Word n) (newer : Vector Word k) (tail : Stack) :
    (run (writeSequence (shiftedWrites writes))
      (newer.toList ++ (locals.toList ++ tail))).map (List.drop (k + n)) = some tail := by
  rw [nested_writes_run]
  simp only [Option.map_some, ← List.append_assoc]
  exact congrArg some (List.drop_left' (by
    simp only [List.length_append, Vector.length_toList]))

theorem nested_writes_remove_prefix {n k : Nat} (writes : NestedWrites n k)
    (locals : Vector Word n) (newer : Vector Word k) (tail : Stack) :
    run (writeSequence (shiftedWrites writes) ++ popPrefix k)
      (newer.toList ++ (locals.toList ++ tail)) =
      some ((updatedLocals locals (oldWrites writes)).toList ++ tail) := by
  apply run_comp (nested_writes_run writes locals newer tail)
  simpa only [Vector.length_toList] using
    popPrefix_run newer.toList ((updatedLocals locals (oldWrites writes)).toList ++ tail)

theorem nested_scope_updates {n k : Nat} (writes : NestedWrites n k)
    (locals : Vector Word n) (newer : Vector Word k) (tail : Stack) :
    run (pushPrefix newer.toList ++ writeSequence (shiftedWrites writes) ++ popPrefix k)
      (locals.toList ++ tail) =
      some ((updatedLocals locals (oldWrites writes)).toList ++ tail) := by
  rw [List.append_assoc]
  exact run_comp (pushPrefix_run newer.toList (locals.toList ++ tail))
    (nested_writes_remove_prefix writes locals newer tail)

theorem nested_scope_exit {n k : Nat} (writes : NestedWrites n k)
    (locals : Vector Word n) (newer : Vector Word k) (tail : Stack) :
    run (pushPrefix locals.toList ++
      (pushPrefix newer.toList ++ writeSequence (shiftedWrites writes) ++ popPrefix k) ++
      popPrefix n) tail = some tail := by
  apply run_comp
  · exact run_comp (pushPrefix_run locals.toList tail)
      (nested_scope_updates writes locals newer tail)
  · simpa only [Vector.length_toList] using
      popPrefix_run (updatedLocals locals (oldWrites writes)).toList tail

theorem write_at_allocated_depth {n k : Nat} (s : Slots n) (locals : Vector Word n)
    (newer : Vector Word k) (i : Fin n) (tail : Stack) (base_matches : tail.length = s.base)
    (accessible : k + i.val < 16) (value : Word) :
    ∃ depth : Fin 16, depth.val = (tail.length + n + k - 1) - s.at i ∧
      run (writeSlot depth) (value :: (newer.toList ++ (locals.toList ++ tail))) =
        some (newer.toList ++ ((locals.set i.val value i.isLt).toList ++ tail)) := by
  refine ⟨⟨k + i.val, accessible⟩, ?_, write_under_prefix locals newer i accessible value tail⟩
  rw [base_matches, Slots.live_depth]

/-- Spare-word bound for actual PUSH/SWAP/POP trace; operand proof is separate. -/
theorem nested_writes_bound {n k : Nat} (writes : NestedWrites n k) (tail : Stack)
    (spare : k + n + tail.length + 1 ≤ 1024) :
    stackBound (writeSequence (shiftedWrites writes)) ((k + n + tail.length : Nat) : Int) =
      true := by
  apply writeSequence_bound_sufficient
  · omega
  · omega

theorem nested_writes_bound_necessary {n k : Nat}
    (first : {i : Fin n // k + i.val < 16} × Word) (rest : NestedWrites n k)
    (tail : Stack) (bounded : stackBound (writeSequence (shiftedWrites (first :: rest)))
      ((k + n + tail.length : Nat) : Int) = true) : k + n + tail.length + 1 ≤ 1024 := by
  exact writeSequence_bound_necessary _ _ _ bounded

#print axioms write_under_prefix
#print axioms read_after_write_under_prefix
#print axioms read_other_after_write_under_prefix
#print axioms write_under_prefix_other
#print axioms nested_writes_read
#print axioms nested_writes_caller
#print axioms nested_writes_run
#print axioms nested_writes_remove_prefix
#print axioms nested_scope_updates
#print axioms nested_scope_exit
#print axioms write_at_allocated_depth
#print axioms nested_writes_bound
#print axioms nested_writes_bound_necessary
end Solidity.Yul.Compilation
